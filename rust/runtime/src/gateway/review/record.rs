//! Signed Delta review and publication boundary records.
use crate::gateway::{Signed, Version};
use cedar_poo_core::CompiledPolicyJson;
use serde::{Deserialize, Serialize};

/// Classification emitted by the existing four-root Lean analyzer.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum AnalysisKind {
    NoGain,
    BranchGain,
    JointGain,
}
/// Exact independently analyzed source, policy, schema and release frontier.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewRecord {
    pub version: Version,
    pub before_root: String,
    pub after_root: String,
    pub before: String,
    pub after: String,
    pub schema: String,
    pub source: String,
    pub epoch: u64,
    pub analysis: AnalysisKind,
    pub evidence: String,
}
/// Separate authority's approval of this exact signed expansion review.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GainApproval {
    pub version: Version,
    pub review: String,
    pub epoch: u64,
}
/// Actual installed successor, bound to the review and preceding publication.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PublicationRecord {
    pub version: Version,
    pub review: Signed,
    pub approval: Option<Signed>,
    pub previous: Option<String>,
    pub epoch: u64,
    pub world: String,
    #[serde(serialize_with = "policy_json")]
    pub policies: CompiledPolicyJson,
}
/// Independently configured original C4 root and full declaration identity.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReleaseIdentity {
    pub root: String,
    pub source: String,
}
/// Publication delivery status; lost replies retain installed state and exposure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum PublicationDelivery {
    Complete,
    LostReply,
}
/// Complete native publication observation, not an execution permit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PublicationView {
    pub root: String,
    pub policies: String,
    pub epoch: u64,
    pub unknown: bool,
    pub publications: usize,
}

fn policy_json<S: serde::Serializer>(
    value: &CompiledPolicyJson,
    writer: S,
) -> Result<S::Ok, S::Error> {
    (**value).serialize(writer)
}
