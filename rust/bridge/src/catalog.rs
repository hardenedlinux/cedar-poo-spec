//! Strict replay of the complete Lean manifest catalog through the existing Cedar runtime.
use cedar_poo_core::CompiledPolicyJson;
use cedar_poo_runtime::{
    Manifest, ReplayMetrics, SchemaEvolutionBundle, ValidatedManifest,
    render_identified_policy_sources, replay_manifest, replay_manifest_measured,
    replay_schema_only_revision, replay_validated_manifest, replay_validated_manifest_measured,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;

pub(crate) fn replay(input: &str) -> Result<Value, String> {
    replay_observed(input, None)
}

pub(crate) fn replay_measured(input: &str, metrics: &mut ReplayMetrics) -> Result<Value, String> {
    replay_observed(input, Some(metrics))
}

fn replay_observed(input: &str, mut metrics: Option<&mut ReplayMetrics>) -> Result<Value, String> {
    let catalog: BTreeMap<String, Value> =
        serde_json::from_str(input).map_err(|e| e.to_string())?;
    if catalog.is_empty() {
        return Err("empty manifest catalog".into());
    }
    let mut output = BTreeMap::new();
    let mut verified = BTreeMap::new();
    let mut handoff = None;
    let mut deployment = None;
    for (name, value) in catalog {
        let result = if value.get("cases").is_some() {
            if value.get("schema").is_some() {
                let manifest: ValidatedManifest =
                    serde_json::from_value(value).map_err(|e| format!("{name}: {e}"))?;
                let receipts = if let Some(stats) = metrics.as_deref_mut() {
                    replay_validated_manifest_measured(&manifest, stats)?
                } else {
                    replay_validated_manifest(&manifest)?
                };
                let result = json!({"kind":"schema-bound","receipts":receipts});
                verified.insert(name.clone(), (manifest, receipts));
                result
            } else {
                let manifest: Manifest =
                    serde_json::from_value(value).map_err(|e| format!("{name}: {e}"))?;
                {
                    let receipts = if let Some(stats) = metrics.as_deref_mut() {
                        replay_manifest_measured(&manifest, stats)?
                    } else {
                        replay_manifest(&manifest)?
                    };
                    json!({"kind":"raw-evaluation","receipts":receipts})
                }
            }
        } else if name == "attested-schema-evolution" {
            let bundle: SchemaEvolutionBundle =
                serde_json::from_value(value).map_err(|e| e.to_string())?;
            json!({"kind":"schema-evolution","receipt":replay_schema_only_revision(&bundle)?})
        } else if name == "pseudonymization-deployable" {
            deployment = Some(value);
            continue;
        } else if name == "pseudonymization-tabular" {
            let fields = value.as_object().ok_or("table fixture must be an object")?;
            let expected = [
                "context",
                "contextField",
                "dataset",
                "keyDomain",
                "tokenKeyVersion",
                "transformVersion",
                "value",
                "valueField",
                "wrappingVersion",
            ];
            if fields.len() != expected.len() + 1
                || !expected
                    .iter()
                    .all(|key| fields.get(*key).is_some_and(Value::is_string))
                || !fields
                    .get("surrogateInfoType")
                    .is_some_and(|value| value.is_null() || value.is_string())
            {
                return Err("unclassified table fixture fields".into());
            }
            json!({"kind":"data-fixture-only"})
        } else if name == "claim-settlement-handoff" {
            handoff = Some(value);
            continue;
        } else {
            return Err(format!("unclassified manifest catalog entry: {name}"));
        };
        output.insert(name, result);
    }
    if let Some(value) = deployment {
        let roots = value
            .as_array()
            .ok_or("deployment roots must be an array")?;
        let expected = BTreeSet::from([
            "HospitalSiv",
            "RandomizedGcm",
            "OneWayHmac",
            "ResultRelease",
            "AgentIncident",
            "Recovered",
        ]);
        let (manifest, _) = verified
            .get("pseudonymization-validated")
            .ok_or("deployment roots require schema-bound replay")?;
        let mut by_root = BTreeMap::new();
        for case in &manifest.cases {
            if let Some(previous) = by_root.insert(case.revision.as_str(), case.policies.deref())
                && previous != case.policies.deref()
            {
                return Err("inconsistent policies for one deployment root".into());
            }
        }
        let mut seen = BTreeSet::new();
        for root in roots {
            let name = root
                .get("root")
                .and_then(Value::as_str)
                .ok_or("missing deployment root")?;
            if !expected.contains(name) || !seen.insert(name) {
                return Err("invalid or duplicate deployment root".into());
            }
            let policies: CompiledPolicyJson = serde_json::from_value(
                root.get("policies")
                    .ok_or("missing deployment policies")?
                    .clone(),
            )
            .map_err(|e| e.to_string())?;
            render_identified_policy_sources(&policies)?;
            if by_root.get(name).copied() != Some(policies.deref()) {
                return Err("deployment policy artifact differs from schema-bound source".into());
            }
        }
        if seen != expected {
            return Err("deployment root topology changed".into());
        }
        output.insert(
            "pseudonymization-deployable".into(),
            json!({"kind":"validated-policy-artifact","roots":seen.len()}),
        );
    }
    if let Some(value) = handoff {
        output.insert(
            "claim-settlement-handoff".into(),
            crate::financial::replay(value, &verified)?,
        );
    } else if verified.contains_key("claim-settlement-claims")
        || verified.contains_key("claim-settlement-banking")
    {
        return Err("settlement schemas require their handoff scenario binding".into());
    }
    serde_json::to_value(output).map_err(|e| e.to_string())
}

/// Fixed complete-catalog samples. Equality/counters gate acceptance; time does not.
pub(crate) fn benchmark(input: &str) -> Result<(), String> {
    let reference = replay(input)?;
    let source: BTreeMap<String, Value> = serde_json::from_str(input).map_err(|e| e.to_string())?;
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
    let mut results = Vec::with_capacity(3);
    for sample in 1..=3 {
        let allocation_before = crate::allocation::snapshot();
        let mut metrics = ReplayMetrics::default();
        let started = std::time::Instant::now();
        let output = replay_measured(input, &mut metrics)?;
        let replay_ns = started.elapsed().as_nanos();
        if output != reference {
            return Err("measured catalog changed complete receipts".into());
        }
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
        results.push(json!({"sample":sample,"allocation":allocation,"unattributed_ns":replay_ns-accounted, "rows":rows, "replay_ns":replay_ns,
            "serialization_ns":serialize_ns, "receipt_bytes":encoded.len(), "runtime":metrics}));
    }
    println!(
        "{}",
        json!({"kind":"native-catalog-benchmark", "build_profile":if cfg!(debug_assertions) { "debug" } else { "release" }, "warmup":1, "samples":results})
    );
    Ok(())
}

#[cfg(test)]
#[path = "../tests/unit/catalog.rs"]
mod tests;
