//! Independent simulated provider journal and signed outcome representation.
use super::wire::{sign, simulation_key};
use super::{Commit, EffectIdentity, FactBinding, Signed, Version, verify};
use crate::json_sha256;
use p256::ecdsa::{SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
/// Independent provider observation of one exact simulated effect.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
pub struct ProviderAction {
    pub effect: EffectIdentity,
    pub result: String,
}
/// Provider-owned journal; auditors receive this independently of gateway receipts.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProviderJournal {
    pub actions: Vec<ProviderAction>,
    // Live provider records cannot be constructed from an unsigned observation.
    #[serde(skip)]
    outcomes: BTreeMap<String, Option<Signed>>,
    #[serde(skip)]
    live: bool,
}
impl Default for ProviderJournal {
    fn default() -> Self {
        Self {
            actions: Vec::new(),
            outcomes: BTreeMap::new(),
            live: true,
        }
    }
}

pub(super) const PROVIDER_OUTCOME_DOMAIN: &str = "cedar-poo/provider-outcome";

/// A provider signature has a distinct domain and independently pinned key.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProviderOutcome {
    pub version: Version,
    pub domain: String,
    pub log_key: Vec<u8>,
    pub outcome: Receipt,
}

pub(super) struct ProviderRequest<'a> {
    pub effect: &'a EffectIdentity,
    pub commit: &'a Signed,
    pub log_key: &'a VerifyingKey,
    pub bindings: &'a [FactBinding],
    pub facts: &'a [Signed],
    pub publications: &'a [Signed],
}

impl ProviderRequest<'_> {
    pub(super) fn validate(&self) -> Result<(), String> {
        let commit: Commit = verify(self.commit, self.log_key)?;
        if commit.version != (Version { major: 1, minor: 0 })
            || commit.effect != *self.effect
            || commit.facts
                != self
                    .bindings
                    .iter()
                    .map(json_sha256)
                    .collect::<Result<Vec<_>, _>>()?
            || commit.publications
                != self
                    .publications
                    .iter()
                    .map(Signed::source_sha256)
                    .collect::<Result<Vec<_>, _>>()?
        {
            return Err("provider input differs from the witnessed intent".into());
        }
        Ok(())
    }

    pub(super) fn sign_outcome(
        &self,
        action: ProviderAction,
        signer: &SigningKey,
    ) -> Result<Signed, String> {
        let outcome = ProviderOutcome {
            version: Version { major: 1, minor: 0 },
            domain: PROVIDER_OUTCOME_DOMAIN.into(),
            log_key: self.log_key.to_encoded_point(false).as_bytes().to_vec(),
            outcome: Receipt {
                version: Version { major: 1, minor: 0 },
                commit: self.commit.clone(),
                action,
                facts: self.facts.to_vec(),
                publications: self.publications.to_vec(),
            },
        };
        sign(&outcome, signer)
    }
}

impl ProviderJournal {
    pub(super) fn observation(action: ProviderAction) -> Self {
        Self {
            actions: vec![action],
            outcomes: BTreeMap::new(),
            live: false,
        }
    }

    /// Detached signed evidence from the provider's actual send boundary.
    /// Deserializing an unsigned journal never creates this evidence.
    pub fn signed_outcomes(&self) -> impl Iterator<Item = &Signed> {
        self.outcomes.values().filter_map(Option::as_ref)
    }
    pub(super) fn send(&mut self, request: ProviderRequest<'_>) -> Result<ProviderAction, String> {
        let effect = request.effect;
        if !self.live || self.outcomes.contains_key(&effect.operation) {
            return Err("provider is an observation or operation already exists".into());
        }
        request.validate()?;
        let action = ProviderAction {
            effect: effect.clone(),
            result: format!("provider-{}", self.outcomes.len()),
        };
        self.actions.push(action.clone());
        // A failed outcome signature cannot undo the effect or permit a resend.
        self.outcomes.insert(
            effect.operation.clone(),
            request
                .sign_outcome(action.clone(), &simulation_key(8))
                .ok(),
        );
        Ok(action)
    }
}
/// Unsigned effect outcome. Gateway signs it directly; providers sign the
/// explicitly domain-separated ProviderOutcome wrapper.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Receipt {
    pub version: Version,
    pub commit: Signed,
    pub action: ProviderAction,
    pub facts: Vec<Signed>,
    pub publications: Vec<Signed>,
}
