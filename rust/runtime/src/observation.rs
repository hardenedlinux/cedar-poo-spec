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
    pub source_policy_reuses: usize,
    pub catalog_policy_reuses: usize,
    pub catalog_syntax_slot_peak: usize,
    pub catalog_syntax_retirements: usize,
    pub revision_syntax_reuses: usize,
    pub schema_preparation_ns: u128,
    /// Source preparation invocations; diagnostic reparses are counted separately.
    pub schema_parse_calls: usize,
    pub schema_diagnostic_reparses: usize,
    pub schema_reuses: usize,
    pub policy_validation_calls: usize,
    pub revision_preparation_ns: u128,
    /// Disjoint subphases of revision preparation, never additional top-level cost.
    pub revision_source_load_ns: u128,
    pub revision_render_ns: u128,
    pub revision_text_parse_ns: u128,
    pub revision_normalize_ns: u128,
    /// Text-side normalization work; reuse is keyed by the complete parsed policy text.
    pub policy_body_normalizations: usize,
    pub policy_body_reuses: usize,
    /// Largest invocation-local set of prepared bodies, not a heap/RSS bound.
    pub policy_body_slot_peak: usize,
    pub revision_compare_ns: u128,
    pub revision_hash_ns: u128,
    pub request_preparation_ns: u128,
    /// Successful UID syntax preparation; requests, contexts and schema checks stay fresh.
    pub uid_parse_calls: usize,
    pub uid_reuses: usize,
    pub uid_slot_peak: usize,
    pub diagnostics_ns: u128,
    pub receipt_ns: u128,
    /// Subphase of request preparation, not an additional top-level duration.
    pub entity_preparation_ns: u128,
    pub entity_hash_calls: usize,
    pub entity_hash_reuses: usize,
    /// Source preparation invocations; diagnostic reparses are counted separately.
    pub entity_parse_calls: usize,
    pub entity_diagnostic_reparses: usize,
    pub entity_reuses: usize,
    pub entity_replacements: usize,
    /// Maximum entries retained by this one-slot owner; not a heap/RSS bound.
    pub entity_slot_peak: usize,
}

/// The ordinary path never reads a clock. Subphases keep their actual owner.
pub(crate) fn revision_phase<T>(
    metrics: Option<&mut ReplayMetrics>,
    phase: fn(&mut ReplayMetrics) -> &mut u128,
    operation: impl FnOnce() -> T,
) -> T {
    match metrics {
        None => operation(),
        Some(stats) => {
            let started = std::time::Instant::now();
            let result = operation();
            *phase(stats) += started.elapsed().as_nanos();
            result
        }
    }
}
