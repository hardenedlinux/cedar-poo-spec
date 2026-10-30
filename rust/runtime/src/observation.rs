//! Optional replay observations shared by preparation and case execution.
use serde::Serialize;
/// Optional observations of the canonical replay, excluding JSON transport.
/// Durations are observations, never authorization inputs or acceptance thresholds.
#[derive(Default, Debug, Serialize)]
pub struct ReplayMetrics {
    pub runtime_preparation_ns: u128,
    pub authorization_ns: u128,
    pub prepared_revisions: usize,
    pub authorization_calls: usize,
    pub source_policy_loads: usize,
    pub schema_preparation_ns: u128,
    pub revision_preparation_ns: u128,
    pub request_preparation_ns: u128,
    pub diagnostics_ns: u128,
    pub receipt_ns: u128,
}
