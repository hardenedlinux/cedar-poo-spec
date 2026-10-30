//! One invocation/schema-bound immutable entity preparation slot.
use crate::observation::ReplayMetrics;
use cedar_policy::{Entities, Schema};
use serde_json::Value;
use std::time::Instant;

pub(crate) struct EntitySlot<'schema, 'input> {
    schema: Option<&'schema Schema>,
    prepared: Option<(&'input Value, Entities)>,
    #[cfg(test)]
    force_fresh: bool,
}
impl<'schema, 'input> EntitySlot<'schema, 'input> {
    pub(crate) fn new(schema: Option<&'schema Schema>) -> Self {
        Self {
            schema,
            prepared: None,
            #[cfg(test)]
            force_fresh: false,
        }
    }
    pub(crate) fn schema(&self) -> Option<&'schema Schema> {
        self.schema
    }
    #[cfg(test)]
    pub(crate) fn uncached(schema: Option<&'schema Schema>) -> Self {
        Self {
            force_fresh: true,
            ..Self::new(schema)
        }
    }
    pub(crate) fn get(
        &mut self,
        source: &'input Value,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<&Entities, String> {
        let started = metrics.as_ref().map(|_| Instant::now());
        let reusable = self
            .prepared
            .as_ref()
            .is_some_and(|(previous, _)| *previous == source);
        #[cfg(test)]
        let reusable = reusable && !self.force_fresh;
        if reusable {
            if let Some(stats) = metrics.as_deref_mut() {
                stats.entity_reuses += 1;
            }
        } else {
            if let Some(stats) = metrics.as_deref_mut() {
                stats.entity_parse_calls += 1;
            }
            // Parse at the original lazy point, before replacing any successful state.
            let parsed = Entities::from_json_value(source.clone(), self.schema)
                .map_err(|error| error.to_string())?;
            if let Some(stats) = metrics.as_deref_mut() {
                stats.entity_replacements += usize::from(self.prepared.is_some());
                stats.entity_slot_peak = 1;
            }
            self.prepared = Some((source, parsed));
        }
        if let (Some(stats), Some(started)) = (metrics, started) {
            stats.entity_preparation_ns += started.elapsed().as_nanos();
        }
        self.prepared
            .as_ref()
            .map(|(_, parsed)| parsed)
            .ok_or_else(|| "missing successfully prepared entities".into())
    }
}

#[cfg(test)]
#[path = "../tests/unit/entities.rs"]
mod tests;
