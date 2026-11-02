//! Fixed native catalog benchmark with explicit lifecycle and cleanup costs.
use crate::catalog::replay_observed;
use crate::catalog_observation::CatalogObservation;
use cedar_poo_runtime::ReplayMetrics;
use serde_json::{Value, json};
use std::time::Instant;

/// Fixed complete-catalog samples. Equality/counters gate acceptance; time does not.
pub(crate) fn run(input: &str, cli_input_read_ns: u128) -> Result<(), String> {
    let body_started = Instant::now();
    let started = Instant::now();
    let mut reference_catalog = CatalogObservation::default();
    let reference = replay_observed(input, None, Some(&mut reference_catalog))?;
    let warmup_ns = started.elapsed().as_nanos();
    let started = Instant::now();
    let inventory = crate::benchmark_inventory::read(input)?;
    let (
        expected_entries,
        expected_revisions,
        expected_source_parses,
        expected_entity_parses,
        expected_schema_bindings,
        expected_validations,
    ) = (
        inventory.entries,
        inventory.revisions,
        inventory.sources,
        inventory.entities,
        inventory.schemas,
        inventory.validations,
    );
    let revision_inventory_ns = started.elapsed().as_nanos();
    let samples_started = Instant::now();
    let mut results = Vec::with_capacity(3);
    let mut measurements = Vec::with_capacity(21);
    for sample in 1..=3 {
        let sample_started = Instant::now();
        let allocation_before = crate::allocation::snapshot();
        let mut metrics = ReplayMetrics::default();
        let started = std::time::Instant::now();
        let mut catalog = CatalogObservation::default();
        let output = replay_observed(input, Some(&mut metrics), Some(&mut catalog))?;
        let replay_ns = started.elapsed().as_nanos();
        let comparison_started = Instant::now();
        if output != reference {
            return Err("measured catalog changed complete receipts".into());
        }
        let comparison_ns = comparison_started.elapsed().as_nanos();
        let started = std::time::Instant::now();
        let encoded = serde_json::to_string(&output).map_err(|e| e.to_string())?;
        let serialize_ns = started.elapsed().as_nanos();
        let rows: usize = output
            .as_object()
            .ok_or("catalog receipts must be an object")?
            .values()
            .filter_map(|value| value.get("receipts").and_then(Value::as_array))
            .map(Vec::len)
            .sum();
        if catalog.entries.len() != expected_entries {
            return Err("incomplete catalog stage observations".into());
        }
        let catalog_accounted = catalog.decode_ns
            + catalog.shared_preparation_ns
            + catalog.entries_ns
            + catalog.finalization_ns
            + catalog.cleanup_ns;
        if catalog_accounted > replay_ns {
            return Err("overlapping catalog stage observations".into());
        }
        if rows == 0
            || metrics.authorization_calls != rows * 2
            || metrics.prepared_revisions != expected_revisions
            || metrics.source_policy_loads != expected_source_parses
            || metrics.source_policy_loads + metrics.source_policy_reuses != expected_revisions
            || metrics.revision_syntax_reuses != metrics.source_policy_reuses
            || metrics.schema_parse_calls + metrics.schema_reuses != expected_schema_bindings
            || metrics.policy_validation_calls != expected_validations
            || metrics.entity_hash_calls + metrics.entity_hash_reuses != rows
            || metrics.schema_diagnostic_reparses != 0
            || metrics.entity_diagnostic_reparses != 0
            || metrics.entity_parse_calls != expected_entity_parses
            || metrics.entity_parse_calls + metrics.entity_reuses != rows
            || metrics.uid_parse_calls + metrics.uid_reuses != rows * 3
            || metrics.uid_slot_peak > metrics.uid_parse_calls
            || metrics.entity_slot_peak != 1
        {
            return Err(
                "measured replay did not execute every compiled/rendered authorization".into(),
            );
        }
        let allocation = allocation_before.zip(crate::allocation::snapshot()).map(|(before, after)| json!({
            "allocation_requests":after[0]-before[0], "requested_bytes":after[1]-before[1],
            "process_requested_live_bytes":after[2], "process_requested_peak_bytes":after[3],
            "scope":"Rust allocator requests; peak is process-wide, excludes allocator overhead and foreign allocations"
        }));
        let accounted = metrics.runtime_preparation_ns
            + metrics.authorization_ns
            + metrics.diagnostics_ns
            + metrics.receipt_ns;
        let revision_accounted = metrics.revision_source_load_ns
            + metrics.revision_render_ns
            + metrics.revision_text_parse_ns
            + metrics.revision_normalize_ns
            + metrics.revision_compare_ns
            + metrics.revision_hash_ns;
        if revision_accounted > metrics.revision_preparation_ns {
            return Err("overlapping revision subphase observations".into());
        }
        if accounted > replay_ns {
            return Err("overlapping replay phase observations".into());
        }
        let receipt_bytes = encoded.len();
        let cleanup_started = Instant::now();
        drop(encoded);
        drop(output);
        let output_cleanup_ns = cleanup_started.elapsed().as_nanos();
        let sample_wall_ns = sample_started.elapsed().as_nanos();
        if replay_ns + comparison_ns + serialize_ns + output_cleanup_ns > sample_wall_ns {
            return Err("overlapping sample lifecycle stages".into());
        }
        for (name, elapsed) in [
            ("replay", replay_ns),
            ("schema_prepare", metrics.schema_preparation_ns),
            ("revision_prepare", metrics.revision_preparation_ns),
            ("normalize", metrics.revision_normalize_ns),
            ("request_prepare", metrics.request_preparation_ns),
            ("authorize", metrics.authorization_ns),
            ("serialize", serialize_ns),
        ] {
            measurements.push((sample, name, elapsed));
        }
        results.push(json!({"sample_wall_ns":sample_wall_ns,"comparison_ns":comparison_ns,"output_cleanup_ns":output_cleanup_ns,"catalog":catalog,"sample":sample,"allocation":allocation,"unattributed_ns":replay_ns-accounted, "rows":rows, "replay_ns":replay_ns,
            "serialization_ns":serialize_ns, "receipt_bytes":receipt_bytes, "runtime":metrics}));
    }
    let samples_ns = samples_started.elapsed().as_nanos();
    let cleanup_started = Instant::now();
    drop(reference);
    let reference_cleanup_ns = cleanup_started.elapsed().as_nanos();
    let measured_body_ns = body_started.elapsed().as_nanos();
    let accounted = warmup_ns + revision_inventory_ns + samples_ns + reference_cleanup_ns;
    let bookkeeping_ns = measured_body_ns
        .checked_sub(accounted)
        .ok_or("overlapping benchmark lifecycle stages")?;
    // Emit after every timed span; formatting/stdio is not SDK preparation.
    for (sample, name, elapsed) in measurements {
        eprintln!("measurement: cedar.sdk.sample{sample}.{name} {elapsed} ns");
    }
    println!(
        "{}",
        json!({"kind":"native-catalog-benchmark", "build_profile":if cfg!(debug_assertions) { "debug" } else { "release" }, "warmup":1, "reference_catalog":reference_catalog, "cli":{"input_read_ns":cli_input_read_ns}, "lifecycle":{"warmup_ns":warmup_ns,"revision_inventory_ns":revision_inventory_ns,"samples_ns":samples_ns,"reference_cleanup_ns":reference_cleanup_ns,"bookkeeping_ns":bookkeeping_ns,"measured_body_ns":measured_body_ns}, "samples":results})
    );
    Ok(())
}
