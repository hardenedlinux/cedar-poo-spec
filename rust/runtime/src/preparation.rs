//! Invocation-owned immutable syntax preparation; never caches requests or decisions.
use crate::observation::ReplayMetrics;
use crate::policy_codec::canonical_policy_body;
use cedar_policy::{EntityUid, PolicySet};
use std::collections::BTreeMap;
use std::str::FromStr;

/// Only the text parser constructs this owner. Consequently every policy has
/// its complete original text; no lossy JSON/PST display is used as identity.
pub(crate) struct ParsedTextPolicies {
    policies: PolicySet,
}

impl ParsedTextPolicies {
    pub(crate) fn policies(&self) -> &PolicySet {
        &self.policies
    }
    pub(crate) fn into_policies(self) -> PolicySet {
        self.policies
    }
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        PolicySet::from_str(text)
            .map(|policies| Self { policies })
            .map_err(|error| format!("rendered Cedar text parse: {error}"))
    }
}

/// One manifest invocation owns pure normalization results, keyed by complete
/// parsed source. SDK 4.12's text-to-JSON conversion reparses that exact text.
/// Hits avoid this repeated EST parse as well as JSON-to-AST normalization.
/// UID entries reuse only successful full-source syntax parses. Context parsing,
/// schema/action validation, Request construction and both authorizers remain per case.
/// Local maps retire at the manifest boundary. Catalog sharing borrows a finite
/// source-use plan; only immutable successful SDK syntax can outlive this owner.
/// Revision names, policy IDs and observed decisions authorize no hit.
#[derive(Default)]
pub(crate) struct PreparedReplay<'catalog> {
    shared: Option<&'catalog mut crate::syntax_preparation::SyntaxPreparation>,
    bodies: BTreeMap<String, String>,
    uids: BTreeMap<String, EntityUid>,
    compiled: BTreeMap<String, std::sync::Arc<PolicySet>>,
    checked: [BTreeMap<String, crate::syntax::CheckedRevision>; 2],
}

impl<'catalog> PreparedReplay<'catalog> {
    pub(crate) fn sharing(
        shared: &'catalog mut crate::syntax_preparation::SyntaxPreparation,
    ) -> Self {
        Self {
            shared: Some(shared),
            ..Self::default()
        }
    }
    pub(crate) fn compiled(
        &mut self,
        source: &crate::CompiledPolicyJson,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<std::sync::Arc<PolicySet>, String> {
        let key = source.source_identity()?;
        if let Some(parsed) = self.compiled.get(key) {
            if let Some(stats) = metrics {
                stats.source_policy_reuses += 1;
            }
            return Ok(parsed.clone());
        }
        if let Some(parsed) = self
            .shared
            .as_deref()
            .and_then(|shared| shared.compiled(key))
        {
            if let Some(stats) = metrics {
                stats.source_policy_reuses += 1;
                stats.catalog_policy_reuses += 1;
            }
            self.compiled.insert(key.to_owned(), parsed.clone());
            return Ok(parsed);
        }
        let parsed = std::sync::Arc::new(crate::policy_codec::load_policy_set(source)?);
        if let Some(shared) = self.shared.as_deref_mut() {
            shared.remember_compiled(key, parsed.clone());
            if let Some(stats) = metrics.as_deref_mut() {
                stats.catalog_syntax_slot_peak =
                    stats.catalog_syntax_slot_peak.max(shared.retained());
            }
        }
        if let Some(stats) = metrics {
            stats.source_policy_loads += 1;
        }
        self.compiled.insert(key.to_owned(), parsed.clone());
        Ok(parsed)
    }
    pub(crate) fn checked(
        &self,
        source: &crate::CompiledPolicyJson,
        hash: bool,
    ) -> Result<Option<crate::syntax::CheckedRevision>, String> {
        let key = source.source_identity()?;
        Ok(self.checked[usize::from(hash)]
            .get(key)
            .cloned()
            .or_else(|| self.shared.as_deref().and_then(|s| s.checked(key, hash))))
    }
    pub(crate) fn remember_checked(
        &mut self,
        checked: crate::syntax::CheckedRevision,
        hash: bool,
    ) -> Result<(), String> {
        let key = checked.source.source_identity()?.to_owned();
        if let Some(shared) = self.shared.as_deref_mut() {
            shared.remember_checked(&key, hash, checked.clone());
        }
        self.checked[usize::from(hash)].insert(key, checked);
        Ok(())
    }
    fn uid(
        &mut self,
        source: &str,
        metrics: Option<&mut ReplayMetrics>,
    ) -> Result<EntityUid, String> {
        if let Some(uid) = self.uids.get(source) {
            if let Some(stats) = metrics {
                stats.uid_reuses += 1;
            }
            return Ok(uid.clone());
        }
        let uid = EntityUid::from_str(source).map_err(|error| error.to_string())?;
        self.uids.insert(source.to_owned(), uid.clone());
        if let Some(stats) = metrics {
            stats.uid_parse_calls += 1;
            stats.uid_slot_peak = stats.uid_slot_peak.max(self.uids.len());
        }
        Ok(uid)
    }

    pub(crate) fn bodies_by_id(
        &mut self,
        parsed: &ParsedTextPolicies,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<BTreeMap<String, String>, String> {
        let mut result = BTreeMap::new();
        for policy in parsed.policies.policies() {
            let key = policy
                .to_cedar()
                .ok_or("parsed static policy has no original Cedar text")?;
            let body = if let Some(body) = self.bodies.get(&key) {
                if let Some(stats) = metrics.as_deref_mut() {
                    stats.policy_body_reuses += 1;
                }
                body.clone()
            } else {
                // The original independent normalizer remains the miss path.
                let body = canonical_policy_body(policy)?;
                self.bodies.insert(key, body.clone());
                if let Some(stats) = metrics.as_deref_mut() {
                    stats.policy_body_normalizations += 1;
                    stats.policy_body_slot_peak =
                        stats.policy_body_slot_peak.max(self.bodies.len());
                }
                body
            };
            // Keep each actual parsed ID and all body multiplicities.
            result.insert(policy.id().to_string(), body);
        }
        Ok(result)
    }
}

pub(crate) fn request_uid(
    source: &str,
    preparation: &mut Option<&mut PreparedReplay>,
    metrics: Option<&mut ReplayMetrics>,
) -> Result<EntityUid, String> {
    if let Some(prepared) = preparation.as_deref_mut() {
        prepared.uid(source, metrics)
    } else {
        let uid = EntityUid::from_str(source).map_err(|error| error.to_string())?;
        if let Some(stats) = metrics {
            stats.uid_parse_calls += 1;
        }
        Ok(uid)
    }
}

#[cfg(test)]
#[path = "../tests/unit/preparation_owner.rs"]
mod tests;
