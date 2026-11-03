//! Independent simulated provider journal and signed outcome representation.
use super::{EffectIdentity, Signed, Version};
use serde::{Deserialize, Serialize};
/// Independent provider observation of one exact simulated effect.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ProviderAction {
    pub effect: EffectIdentity,
    pub result: String,
}
/// Provider-owned journal; auditors receive this independently of gateway receipts.
#[derive(Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProviderJournal {
    pub actions: Vec<ProviderAction>,
}
impl ProviderJournal {
    pub(super) fn send(&mut self, effect: &EffectIdentity) -> Result<ProviderAction, String> {
        if self
            .actions
            .iter()
            .any(|action| action.effect.operation == effect.operation)
        {
            return Err("provider operation already exists".into());
        }
        let action = ProviderAction {
            effect: effect.clone(),
            result: format!("provider-{}", self.actions.len()),
        };
        self.actions.push(action.clone());
        Ok(action)
    }
}
/// Gateway outcome with signed precommit and original source evidence.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Receipt {
    pub version: Version,
    pub commit: Signed,
    pub action: ProviderAction,
    pub facts: Vec<Signed>,
    pub publications: Vec<Signed>,
}
