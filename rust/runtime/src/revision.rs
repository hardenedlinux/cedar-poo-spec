//! Sealed revision source binding and immutable independently checked SDK syntax.
use crate::CompiledPolicyJson;
use crate::canonical::value_sha256;
use crate::input::Case;
use crate::observation::{ReplayMetrics, revision_phase};
use crate::policy_codec::{
    load_policy_set, policy_bodies_by_id, policy_body_counts, rendered_policy_bodies,
};
use crate::preparation::{ParsedTextPolicies, PreparedReplay};
use crate::syntax::CheckedRevision;
use cedar_policy::PolicySet;
use std::ops::Deref;
use std::time::Instant;

/// A sealed source/parse pair. Validation can borrow it but cannot replace its body.
pub(crate) struct SourcePolicies {
    revision: String,
    source: CompiledPolicyJson,
    policies: std::sync::Arc<PolicySet>,
}
impl SourcePolicies {
    pub(crate) fn new(case: &Case) -> Result<Self, String> {
        Ok(Self {
            revision: case.revision.clone(),
            source: case.policies.clone(),
            policies: std::sync::Arc::new(load_policy_set(&case.policies)?),
        })
    }
    pub(crate) fn prepared(
        case: &Case,
        metrics: Option<&mut ReplayMetrics>,
        prepared: Option<&mut PreparedReplay>,
    ) -> Result<Self, String> {
        if let Some(prepared) = prepared {
            let policies = prepared.compiled(&case.policies, metrics)?;
            Ok(Self {
                revision: case.revision.clone(),
                source: case.policies.clone(),
                policies,
            })
        } else {
            if let Some(stats) = metrics {
                stats.source_policy_loads += 1;
            }
            Self::new(case)
        }
    }
    pub(crate) fn policies(&self) -> &PolicySet {
        &self.policies
    }
    pub(crate) fn checked(
        self,
        case: &Case,
        hash_for_receipt: bool,
        metrics: Option<&mut ReplayMetrics>,
        bodies: Option<&mut PreparedReplay>,
    ) -> Result<CheckedRevision, String> {
        if self.revision != case.revision
            || (!self.source.same_source(&case.policies) && *self.source != *case.policies.deref())
        {
            return Err("prepared policy source mismatch".into());
        }
        let mut metrics = metrics;
        let mut bodies = bodies;
        let cached = match bodies.as_deref() {
            Some(p) => p.checked(&self.source, hash_for_receipt)?,
            None => None,
        };
        if let Some(mut cached) = cached {
            if let Some(stats) = metrics.as_deref_mut() {
                stats.revision_syntax_reuses += 1;
            }
            // The pure syntax is equal; bind each revision to its current owner.
            cached.source = self.source;
            return Ok(cached);
        }
        let checked =
            CheckedRevision::from_source(self, hash_for_receipt, metrics, bodies.as_deref_mut())?;
        if let Some(prepared) = bodies {
            prepared.remember_checked(checked.clone(), hash_for_receipt)?;
        }
        Ok(checked)
    }
}
impl CheckedRevision {
    pub(crate) fn new(
        case: &Case,
        hash_for_receipt: bool,
        mut metrics: Option<&mut ReplayMetrics>,
        bodies: Option<&mut PreparedReplay>,
    ) -> Result<Self, String> {
        let mut bodies = bodies;
        let started = metrics.as_ref().map(|_| Instant::now());
        let source = SourcePolicies::prepared(case, metrics.as_deref_mut(), bodies.as_deref_mut())?;
        if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
            stats.revision_source_load_ns += started.elapsed().as_nanos();
        }
        source.checked(case, hash_for_receipt, metrics, bodies)
    }
    fn from_source(
        source: SourcePolicies,
        hash_for_receipt: bool,
        mut metrics: Option<&mut ReplayMetrics>,
        mut bodies: Option<&mut PreparedReplay>,
    ) -> Result<Self, String> {
        let SourcePolicies {
            source, policies, ..
        } = source;
        // SourcePolicies is sealed and loaded exclusively through Policy::from_json.
        // to_cedar already renders its normalized AST; retain those exact bodies.
        let (text, compiled_bodies) = revision_phase(
            metrics.as_deref_mut(),
            |s| &mut s.revision_render_ns,
            || rendered_policy_bodies(&policies),
        )?;
        let rendered = revision_phase(
            metrics.as_deref_mut(),
            |s| &mut s.revision_text_parse_ns,
            || ParsedTextPolicies::parse(&text),
        )?;
        // A source miss parses rendered text independently of the compiled AST.
        // The complete immutable source keys reuse; revision bindings, strict
        // schema validation and both authorizers remain independent.
        let normalize_started = metrics.as_ref().map(|_| Instant::now());
        let rendered_bodies = if let Some(prepared) = bodies.as_mut() {
            prepared.bodies_by_id(&rendered, metrics.as_deref_mut())
        } else {
            policy_bodies_by_id(rendered.policies())
        };
        if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), normalize_started) {
            stats.revision_normalize_ns += started.elapsed().as_nanos();
        }
        let rendered_bodies = rendered_bodies?;
        let same = revision_phase(
            metrics.as_deref_mut(),
            |s| &mut s.revision_compare_ns,
            || policy_body_counts(&compiled_bodies) == policy_body_counts(&rendered_bodies),
        );
        if !same {
            return Err("rendered Cedar text changed policy bodies".into());
        }
        let policy_sha256 = revision_phase(
            metrics,
            |s| &mut s.revision_hash_ns,
            || {
                if hash_for_receipt {
                    value_sha256(&source).map(Some)
                } else {
                    Ok(None)
                }
            },
        )?;
        Ok(Self {
            source,
            policy_sha256,
            policies,
            rendered: std::sync::Arc::new(rendered.into_policies()),
            compiled_bodies: std::sync::Arc::new(compiled_bodies),
            rendered_bodies: std::sync::Arc::new(rendered_bodies),
        })
    }
}
