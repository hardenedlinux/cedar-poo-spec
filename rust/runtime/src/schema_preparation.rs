//! Explicit source-bound schema lifetime across related manifest replays.
use crate::observation::ReplayMetrics;
use cedar_policy::{Schema, Validator};
use cedar_poo_core::{JsonSourceIdentity, SchemaSourceJson};
use serde_json::Value;
use std::sync::{Arc, OnceLock};

pub(crate) struct PreparedSchema {
    source: Value,
    pub(crate) validator: Validator,
    digest: OnceLock<String>,
}
impl PreparedSchema {
    pub(crate) fn parse(
        source: &Value,
        metrics: Option<&mut ReplayMetrics>,
    ) -> Result<Arc<Self>, String> {
        if let Some(stats) = metrics {
            stats.schema_parse_calls += 1;
        }
        let schema =
            Schema::from_json_value(source.clone()).map_err(|e| format!("Cedar schema: {e}"))?;
        Ok(Arc::new(Self {
            source: source.clone(),
            validator: Validator::new(schema),
            digest: OnceLock::new(),
        }))
    }
    pub(crate) fn digest(&self) -> Result<&str, String> {
        if self.digest.get().is_none() {
            let value = crate::canonical::value_sha256(&self.source)?;
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
        let mut slots = std::collections::BTreeMap::new();
        for source in sources {
            let slot = slots.entry(source.encode_source()?).or_insert(Slot {
                remaining: 0,
                prepared: None,
            });
            slot.remaining += 1;
        }
        slots.retain(|_, slot| slot.remaining > 1);
        Ok(Self { slots })
    }
    pub(crate) fn acquire(
        &mut self,
        source: &Value,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<Arc<PreparedSchema>, String> {
        let started = metrics.as_ref().map(|_| std::time::Instant::now());
        let key = source.encode_source()?;
        let prepared = if let Some(slot) = self.slots.get_mut(&key) {
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
                self.slots.remove(&key);
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
