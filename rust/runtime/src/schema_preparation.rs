//! Explicit source-bound schema lifetime across related manifest replays.
use crate::observation::ReplayMetrics;
use cedar_policy::{Schema, Validator};
use cedar_poo_core::SchemaSourceJson;
use std::sync::{Arc, OnceLock};

pub(crate) struct PreparedSchema {
    source: SchemaSourceJson,
    pub(crate) validator: Validator,
    digest: OnceLock<String>,
}
impl PreparedSchema {
    pub(crate) fn parse(
        source: &SchemaSourceJson,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<Arc<Self>, String> {
        if let Some(stats) = metrics.as_deref_mut() {
            stats.schema_parse_calls += 1;
        }
        // The complete canonical wire is already owned for source identity. Parse
        // it directly instead of cloning a JSON tree solely for SDK ownership.
        // The original Value route preserves exact diagnostics on rejection.
        let schema = match Schema::from_json_str(source.source_identity()?) {
            Ok(schema) => schema,
            Err(_) => {
                if let Some(stats) = metrics {
                    stats.schema_diagnostic_reparses += 1;
                }
                Schema::from_json_value((**source).clone())
                    .map_err(|e| format!("Cedar schema: {e}"))?
            }
        };
        Ok(Arc::new(Self {
            source: source.clone(),
            validator: Validator::new(schema),
            digest: OnceLock::new(),
        }))
    }
    pub(crate) fn digest(&self) -> Result<&str, String> {
        if self.digest.get().is_none() {
            let value = crate::canonical::schema_sha256(&self.source)?;
            let _ = self.digest.set(value);
        }
        self.digest
            .get()
            .map(String::as_str)
            .ok_or_else(|| "missing prepared schema digest".into())
    }
}
struct Slot {
    remaining: usize,
    prepared: Option<Arc<PreparedSchema>>,
}
/// Finite source-use plan for immutable schema preparation, never admission.
/// Unshared inputs are not retained; shared SDK state retires on its last use.
#[derive(Default)]
pub struct SchemaPreparation {
    slots: std::collections::BTreeMap<String, Slot>,
}
impl SchemaPreparation {
    /// Declare shared source uses without parsing or admitting any schema.
    pub fn from_sources(
        sources: impl IntoIterator<Item = SchemaSourceJson>,
    ) -> Result<Self, String> {
        // Count borrowed complete identities while immutable source owners live.
        // Shared keys allocate once; one-use sources do not enter the retained plan.
        let sources = sources.into_iter().collect::<Vec<_>>();
        let mut counts = std::collections::BTreeMap::<&str, usize>::new();
        for source in &sources {
            *counts.entry(source.source_identity()?).or_default() += 1;
        }
        let slots = counts
            .into_iter()
            .filter(|(_, n)| *n > 1)
            .map(|(key, remaining)| {
                (
                    key.to_owned(),
                    Slot {
                        remaining,
                        prepared: None,
                    },
                )
            })
            .collect();
        Ok(Self { slots })
    }
    pub(crate) fn acquire(
        &mut self,
        source: &SchemaSourceJson,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<Arc<PreparedSchema>, String> {
        let started = metrics.as_ref().map(|_| std::time::Instant::now());
        let key = source.source_identity()?;
        let prepared = if let Some(slot) = self.slots.get_mut(key) {
            let schema = if let Some(schema) = &slot.prepared {
                if let Some(stats) = metrics.as_deref_mut() {
                    stats.schema_reuses += 1;
                }
                schema.clone()
            } else {
                let schema = PreparedSchema::parse(source, metrics.as_deref_mut())?;
                slot.prepared = Some(schema.clone());
                schema
            };
            slot.remaining -= 1;
            if slot.remaining == 0 {
                self.slots.remove(key);
            }
            schema
        } else {
            PreparedSchema::parse(source, metrics.as_deref_mut())?
        };
        if let (Some(stats), Some(started)) = (metrics, started) {
            let elapsed = started.elapsed().as_nanos();
            stats.runtime_preparation_ns += elapsed;
            stats.schema_preparation_ns += elapsed;
        }
        Ok(prepared)
    }
}

/// Immutable, strictly validated Schema/Policy sources owned by one live program.
/// Request/entity parsing, both authorizers and receipt expectations remain fresh.
/// Clones share only successful source preparation; no request or Allow is retained.
#[derive(Clone)]
pub struct ValidatedProgram {
    schema: Arc<PreparedSchema>,
    revision: crate::syntax::CheckedRevision,
}
impl ValidatedProgram {
    /// Digest of the exact immutable Schema bound to this source owner.
    pub fn schema_sha256(&self) -> Result<&str, String> {
        self.schema.digest()
    }

    /// Prepare sources and evaluate the first Case exactly once.
    pub fn prepare(
        source: &SchemaSourceJson,
        case: &crate::Case,
    ) -> Result<(Self, crate::SchemaBoundReceipt), String> {
        Self::prepare_using(PreparedSchema::parse(source, None)?, case)
    }
    fn prepare_using(
        schema: Arc<PreparedSchema>,
        case: &crate::Case,
    ) -> Result<(Self, crate::SchemaBoundReceipt), String> {
        let manifest = crate::ValidatedManifest {
            schema: schema.source.clone(),
            cases: vec![case.clone()],
        };
        let mut preparation = crate::preparation::PreparedReplay::default();
        let receipt =
            crate::schema::replay_with_schema_using(&manifest, &schema, None, &mut preparation)?
                .into_iter()
                .next()
                .ok_or("missing prepared program receipt")?;
        let revision = preparation
            .checked(&case.policies, true)?
            .ok_or("missing checked program source")?;
        Ok((Self { schema, revision }, receipt))
    }
    /// Validate a replacement policy against this exact Schema; unchanged full
    /// sources reuse successful preparation, including annotation/source identity.
    pub fn revise(&self, case: &crate::Case) -> Result<(Self, crate::SchemaBoundReceipt), String> {
        if self.revision.source.same_source(&case.policies) {
            Ok((self.clone(), self.replay(case)?))
        } else {
            Self::prepare_using(self.schema.clone(), case)
        }
    }
    /// Evaluate a fresh Case under the bound Schema and exact original policies.
    pub fn replay(&self, case: &crate::Case) -> Result<crate::SchemaBoundReceipt, String> {
        self.replay_observed(case, None)
    }
    /// Observe reuse without changing source checks or authorizer execution.
    pub fn replay_measured(
        &self,
        case: &crate::Case,
        metrics: &mut ReplayMetrics,
    ) -> Result<crate::SchemaBoundReceipt, String> {
        self.replay_observed(case, Some(metrics))
    }
    fn replay_observed(
        &self,
        case: &crate::Case,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<crate::SchemaBoundReceipt, String> {
        if !self.revision.source.same_source(&case.policies) {
            return Err("prepared program policy source changed".into());
        }
        if let Some(stats) = metrics.as_deref_mut() {
            stats.schema_reuses += 1;
            stats.source_policy_reuses += 1;
            stats.revision_syntax_reuses += 1;
        }
        let replay = crate::replay::replay_checked_case(
            case,
            &self.revision,
            self.schema.validator.schema(),
            metrics,
        )?;
        Ok(crate::SchemaBoundReceipt {
            schema_sha256: self.schema.digest()?.to_owned(),
            replay,
        })
    }
}

#[cfg(test)]
#[path = "../tests/unit/validated_program.rs"]
mod program_tests;
