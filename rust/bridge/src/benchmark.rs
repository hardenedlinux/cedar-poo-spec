//! Fixed native catalog benchmark with explicit lifecycle and cleanup costs.
use crate::catalog::{replay, replay_observed};
use crate::catalog_observation::CatalogObservation;
use cedar_poo_runtime::ReplayMetrics;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

/// Fixed complete-catalog samples. Equality/counters gate acceptance; time does not.
pub(crate) fn run(input: &str, cli_input_read_ns: u128) -> Result<(), String> {
    let body_started = Instant::now();
    let started = Instant::now();
    let reference = replay(input)?;
    let warmup_ns = started.elapsed().as_nanos();
    let started = Instant::now();
    let source: BTreeMap<String, Value> = serde_json::from_str(input).map_err(|e| e.to_string())?;
    let expected_entries = source.len();
    let expected_revisions: usize = source
        .values()
        .filter_map(|entry| entry.get("cases").and_then(Value::as_array))
        .map(|cases| {
            cases
                .iter()
                .filter_map(|case| case.get("revision").and_then(Value::as_str))
                .collect::<BTreeSet<_>>()
                .len()
        })
        .sum();

    drop(source);
    let revision_inventory_ns = started.elapsed().as_nanos();
    let samples_started = Instant::now();
    let mut results = Vec::with_capacity(3);
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
        let catalog_accounted =
            catalog.decode_ns + catalog.entries_ns + catalog.finalization_ns + catalog.cleanup_ns;
        if catalog_accounted > replay_ns {
            return Err("overlapping catalog stage observations".into());
        }
        if rows == 0
            || metrics.authorization_calls != rows * 2
            || metrics.prepared_revisions != expected_revisions
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
    println!(
        "{}",
        json!({"kind":"native-catalog-benchmark", "build_profile":if cfg!(debug_assertions) { "debug" } else { "release" }, "warmup":1, "cli":{"input_read_ns":cli_input_read_ns}, "lifecycle":{"warmup_ns":warmup_ns,"revision_inventory_ns":revision_inventory_ns,"samples_ns":samples_ns,"reference_cleanup_ns":reference_cleanup_ns,"bookkeeping_ns":bookkeeping_ns,"measured_body_ns":measured_body_ns}, "samples":results})
    );
    Ok(())
}
