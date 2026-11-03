//! Verified-log lineage and indexed source-to-operation dependency queries.
use super::{LogSnapshot, ProviderJournal, Witness, verify_log};
use p256::ecdsa::VerifyingKey;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
/// Distinct evidence states; a precommit is not a provider observation.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum LineageState {
    PrecommittedOnly,
    ProviderObserved,
}
/// Versioned graph-neutral source batch, not a physical GraphAr file.
#[derive(Clone, Debug, Serialize)]
pub struct LineageBatch {
    pub format_version: u64,
    pub kind: &'static str,
    pub edges: Vec<LineageEdge>,
}
/// Kind-separated lineage edges retain precommit/outcome distinction.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct LineageEdge {
    pub source: String,
    pub operation: String,
    pub state: LineageState,
}
/// Verified-log source index; records dependencies without granting authority.
#[derive(Default)]
pub struct Lineage {
    by_source: BTreeMap<String, BTreeSet<String>>,
    edges: Vec<LineageEdge>,
}
impl Lineage {
    pub fn from_witness(witness: &Witness, provider: &ProviderJournal) -> Result<Self, String> {
        Self::from_snapshot(
            &witness.snapshot(),
            &witness.verifying_key(),
            witness.minimum_size(),
            provider,
        )
    }
    pub fn from_snapshot(
        snapshot: &LogSnapshot,
        key: &VerifyingKey,
        minimum_size: u64,
        provider: &ProviderJournal,
    ) -> Result<Self, String> {
        let mut lineage = Self::default();
        let observed: BTreeSet<_> = provider
            .actions
            .iter()
            .map(|action| &action.effect)
            .collect();
        for commit in verify_log(snapshot, key, minimum_size)? {
            let state = if observed.contains(&commit.effect) {
                LineageState::ProviderObserved
            } else {
                LineageState::PrecommittedOnly
            };
            for source in commit.facts {
                lineage
                    .by_source
                    .entry(source.clone())
                    .or_default()
                    .insert(commit.effect.operation.clone());
                lineage.edges.push(LineageEdge {
                    source,
                    operation: commit.effect.operation.clone(),
                    state: state.clone(),
                });
            }
        }
        Ok(lineage)
    }
    pub fn affected(&self, sources: &[String]) -> BTreeSet<String> {
        sources
            .iter()
            .filter_map(|source| self.by_source.get(source))
            .flat_map(|operations| operations.iter().cloned())
            .collect()
    }
    /// Versioned graph-neutral batch for a consumer-owned GraphAr/Arrow adapter.
    /// It is not a GraphAr file format, completeness certificate or permission.
    pub fn export(&self) -> LineageBatch {
        LineageBatch {
            format_version: 1,
            kind: "cedar-poo-source-lineage",
            edges: self.edges.clone(),
        }
    }
}
