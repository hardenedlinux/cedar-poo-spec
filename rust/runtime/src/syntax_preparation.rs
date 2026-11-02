//! Finite cross-manifest reuse of immutable SDK syntax, never admission.
use crate::{CompiledPolicyJson, syntax::CheckedRevision};
use cedar_policy::PolicySet;
use std::{collections::BTreeMap, sync::Arc};

struct Slot {
    remaining: usize,
    compiled: Option<Arc<PolicySet>>,
    checked: [Option<CheckedRevision>; 2],
}
#[derive(Default)]
pub(crate) struct SyntaxPreparation {
    slots: BTreeMap<String, Slot>,
}
impl SyntaxPreparation {
    pub(crate) fn plan(
        uses: impl IntoIterator<Item = Vec<CompiledPolicyJson>>,
    ) -> Result<Self, String> {
        // First count borrowed full identities while immutable source owners live.
        // Copy keys only for shared sources; one-use sources never allocate a
        // catalog-owned encoding merely to be discarded after planning.
        let uses = uses.into_iter().collect::<Vec<_>>();
        let mut counts = BTreeMap::<&str, usize>::new();
        for sources in &uses {
            let keys = sources
                .iter()
                .map(|s| s.source_identity())
                .collect::<Result<std::collections::BTreeSet<_>, _>>()?;
            for key in keys {
                *counts.entry(key).or_default() += 1;
            }
        }
        let slots = counts
            .into_iter()
            .filter(|(_, remaining)| *remaining > 1)
            .map(|(key, remaining)| {
                (
                    key.to_owned(),
                    Slot {
                        remaining,
                        compiled: None,
                        checked: [None, None],
                    },
                )
            })
            .collect();
        Ok(Self { slots })
    }
    pub(crate) fn compiled(&self, key: &str) -> Option<Arc<PolicySet>> {
        self.slots.get(key)?.compiled.clone()
    }
    pub(crate) fn remember_compiled(&mut self, key: &str, value: Arc<PolicySet>) {
        if let Some(slot) = self.slots.get_mut(key) {
            slot.compiled = Some(value);
        }
    }
    pub(crate) fn checked(&self, key: &str, hash: bool) -> Option<CheckedRevision> {
        self.slots.get(key)?.checked[usize::from(hash)].clone()
    }
    pub(crate) fn remember_checked(&mut self, key: &str, hash: bool, value: CheckedRevision) {
        if let Some(slot) = self.slots.get_mut(key) {
            slot.checked[usize::from(hash)] = Some(value);
        }
    }
    pub(crate) fn finish(&mut self, sources: &[crate::Case]) -> Result<usize, String> {
        let keys = sources
            .iter()
            .map(|c| c.policies.source_identity())
            .collect::<Result<std::collections::BTreeSet<_>, _>>()?;
        let mut retired = 0;
        for key in keys {
            if let Some(slot) = self.slots.get_mut(key) {
                slot.remaining -= 1;
                if slot.remaining == 0 {
                    self.slots.remove(key);
                    retired += 1;
                }
            }
        }
        Ok(retired)
    }
    pub(crate) fn retained(&self) -> usize {
        self.slots.values().filter(|s| s.compiled.is_some()).count()
    }
}

#[cfg(test)]
#[path = "../tests/unit/syntax_preparation_owner.rs"]
mod tests;
