//! Immutable SDK syntax contract consumed by preparation and case execution.
use crate::CompiledPolicyJson;
use cedar_policy::PolicySet;
use std::collections::BTreeMap;

#[derive(Clone)]
pub(crate) struct CheckedRevision {
    pub(crate) source: CompiledPolicyJson,
    pub(crate) policy_sha256: Option<String>,
    pub(crate) policies: std::sync::Arc<PolicySet>,
    pub(crate) rendered: std::sync::Arc<PolicySet>,
    pub(crate) compiled_bodies: std::sync::Arc<BTreeMap<String, String>>,
    pub(crate) rendered_bodies: std::sync::Arc<BTreeMap<String, String>>,
}
