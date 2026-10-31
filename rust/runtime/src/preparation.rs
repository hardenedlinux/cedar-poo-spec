//! Invocation-owned immutable syntax preparation; never caches requests or decisions.
use crate::observation::ReplayMetrics;
use cedar_policy::{EntityUid, PolicySet};
use std::collections::BTreeMap;
use std::str::FromStr;

/// Only the text parser constructs this owner. Consequently every policy has
/// its complete original text; no lossy JSON/PST display is used as identity.
pub(crate) struct ParsedTextPolicies {
    policies: PolicySet,
}

impl ParsedTextPolicies {
    pub(crate) fn policies(&self) -> &PolicySet {
        &self.policies
    }
    pub(crate) fn into_policies(self) -> PolicySet {
        self.policies
    }
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        PolicySet::from_str(text)
            .map(|policies| Self { policies })
            .map_err(|error| format!("rendered Cedar text parse: {error}"))
    }
}

/// One manifest invocation owns pure normalization results, keyed by complete
/// parsed source. SDK 4.12's text-to-JSON conversion reparses that exact text.
/// Hits avoid this repeated EST parse as well as JSON-to-AST normalization.
/// UID entries reuse only successful full-source syntax parses. Context parsing,
/// schema/action validation, Request construction and both authorizers remain per case.
/// The entire owner retires at the manifest invocation boundary.
/// Revision names, policy IDs and observed decisions authorize no hit.
#[derive(Default)]
pub(crate) struct PreparedReplay {
    bodies: BTreeMap<String, String>,
    uids: BTreeMap<String, EntityUid>,
}

impl PreparedReplay {
    fn uid(
        &mut self,
        source: &str,
        metrics: Option<&mut ReplayMetrics>,
    ) -> Result<EntityUid, String> {
        if let Some(uid) = self.uids.get(source) {
            if let Some(stats) = metrics {
                stats.uid_reuses += 1;
            }
            return Ok(uid.clone());
        }
        let uid = EntityUid::from_str(source).map_err(|error| error.to_string())?;
        self.uids.insert(source.to_owned(), uid.clone());
        if let Some(stats) = metrics {
            stats.uid_parse_calls += 1;
            stats.uid_slot_peak = stats.uid_slot_peak.max(self.uids.len());
        }
        Ok(uid)
    }

    pub(crate) fn bodies_by_id(
        &mut self,
        parsed: &ParsedTextPolicies,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<BTreeMap<String, String>, String> {
        let mut result = BTreeMap::new();
        for policy in parsed.policies.policies() {
            let key = policy
                .to_cedar()
                .ok_or("parsed static policy has no original Cedar text")?;
            let body = if let Some(body) = self.bodies.get(&key) {
                if let Some(stats) = metrics.as_deref_mut() {
                    stats.policy_body_reuses += 1;
                }
                body.clone()
            } else {
                // The original independent normalizer remains the miss path.
                let body = canonical_policy_body(policy)?;
                self.bodies.insert(key, body.clone());
                if let Some(stats) = metrics.as_deref_mut() {
                    stats.policy_body_normalizations += 1;
                    stats.policy_body_slot_peak =
                        stats.policy_body_slot_peak.max(self.bodies.len());
                }
                body
            };
            // Keep each actual parsed ID and all body multiplicities.
            result.insert(policy.id().to_string(), body);
        }
        Ok(result)
    }
}

pub(crate) fn request_uid(
    source: &str,
    preparation: &mut Option<&mut PreparedReplay>,
    metrics: Option<&mut ReplayMetrics>,
) -> Result<EntityUid, String> {
    if let Some(prepared) = preparation.as_deref_mut() {
        prepared.uid(source, metrics)
    } else {
        let uid = EntityUid::from_str(source).map_err(|error| error.to_string())?;
        if let Some(stats) = metrics {
            stats.uid_parse_calls += 1;
        }
        Ok(uid)
    }
}

pub(crate) fn canonical_policy_body(policy: &cedar_policy::Policy) -> Result<String, String> {
    let json = policy
        .to_json()
        .map_err(|error| format!("Cedar policy JSON: {error}"))?;
    let normalized = cedar_policy::Policy::from_json(None, json)
        .map_err(|error| format!("Cedar policy normalization: {error}"))?;
    normalized
        .to_cedar()
        .ok_or_else(|| "normalized Cedar policy has no source".into())
}

#[cfg(test)]
#[path = "../tests/unit/preparation_owner.rs"]
mod tests;
