//! Wire contracts and immutable-source normalization; no SDK admission.
use crate::CompiledPolicyJson;
use serde::{Deserialize, Deserializer, Serialize};
use serde_json::Value;
use std::collections::BTreeMap;

/// Request fields emitted from the Lean Cedar model.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct RequestInput {
    pub principal: String,
    pub action: String,
    pub resource: String,
    pub context: Value,
}

/// One concrete authorization case and its Lean-computed receipt.
#[derive(Debug, Clone, Deserialize)]
pub struct Case {
    pub name: String,
    pub revision: String,
    pub policy_ids: Vec<String>,
    pub policies: CompiledPolicyJson,
    pub entities: cedar_poo_core::EntitySourceJson,
    pub request: RequestInput,
    pub expected: String,
    pub expected_reasons: Vec<String>,
    pub expected_error_policies: Vec<String>,
}

/// Bundle of Lean-computed cases for the official Cedar engine.
#[derive(Debug, Deserialize)]
pub struct Manifest {
    #[serde(deserialize_with = "crate::input::cases")]
    pub cases: Vec<Case>,
}

/// A reproducible record of one official Cedar replay, not a Lean proof or a signature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayReceipt {
    pub format_version: u32,
    pub cedar_policy_version: String,
    pub cedar_language_version: String,
    pub case_name: String,
    pub revision: String,
    pub policies_sha256: String,
    pub entities_sha256: String,
    pub request_sha256: String,
    pub decision: String,
    pub reasons: Vec<String>,
    pub error_policy_ids: Vec<String>,
    /// Conservative deployment signal; Cedar's decision remains recorded separately.
    pub error_free_allow: bool,
}

pub(crate) fn valid_revision_name(revision: &str) -> bool {
    revision.split('.').all(|segment| {
        !segment.is_empty()
            && segment
                .chars()
                .all(|character| character.is_ascii_alphanumeric() || character == '-')
    })
}

pub(crate) fn cases<'de, D: Deserializer<'de>>(decoder: D) -> Result<Vec<Case>, D::Error> {
    let mut cases = Vec::<Case>::deserialize(decoder)?;
    let mut sources = BTreeMap::new();
    for case in &mut cases {
        if let Some(source) = sources.get(&case.revision) {
            let source: &crate::CompiledPolicyJson = source;
            if source.same_source(&case.policies) {
                case.policies = source.clone();
            }
            // Conflicts remain unchanged and are rejected at their original point.
        } else {
            sources.insert(case.revision.clone(), case.policies.clone());
        }
    }
    Ok(cases)
}
