//! Strict replay of the complete Lean manifest catalog through the existing Cedar runtime.
use crate::catalog_observation::{
    CatalogObservation, memory_end, memory_end_entry, memory_start, record,
};
use cedar_poo_core::CompiledPolicyJson;
use cedar_poo_runtime::{
    Manifest, ReplayMetrics, SchemaEvolutionBundle, ValidatedManifest,
    render_identified_policy_sources, replay_manifest, replay_manifest_measured,
    replay_schema_only_revision,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;
use std::time::Instant;

pub(crate) fn replay(input: &str) -> Result<Value, String> {
    replay_observed(input, None, None)
}

pub(crate) fn replay_observed(
    input: &str,
    mut metrics: Option<&mut ReplayMetrics>,
    mut observation: Option<&mut CatalogObservation>,
) -> Result<Value, String> {
    let memory = memory_start(&observation);
    let decode = observation.as_ref().map(|_| Instant::now());
    let catalog = crate::catalog_input::decode(input)?;
    memory_end(&mut observation, "decode", memory);
    if catalog.is_empty() {
        return Err("empty manifest catalog".into());
    }
    if let (Some(observation), Some(started)) = (observation.as_deref_mut(), decode) {
        observation.decode_ns = started.elapsed().as_nanos();
    }
    let memory = memory_start(&observation);
    let planned = observation.as_ref().map(|_| Instant::now());
    let mut schemas = cedar_poo_runtime::SchemaPreparation::from_sources(
        crate::catalog_input::schema_sources(&catalog),
    )?;
    if let (Some(observation), Some(started)) = (observation.as_deref_mut(), planned) {
        observation.shared_preparation_ns = started.elapsed().as_nanos();
    }
    memory_end(&mut observation, "schema-plan", memory);
    let entries_started = observation.as_ref().map(|_| Instant::now());
    let mut output = BTreeMap::new();
    let mut verified = BTreeMap::new();
    let mut handoff = None;
    let mut deployment = None;
    for (name, raw) in catalog {
        let memory = memory_start(&observation);
        let started = observation.as_ref().map(|_| Instant::now());
        let value = crate::catalog_input::value(raw)?;
        let result = if value.get("cases").is_some() {
            if value.get("schema").is_some() {
                let manifest: ValidatedManifest =
                    serde_json::from_value(value).map_err(|e| format!("{name}: {e}"))?;
                let receipts = schemas.replay(&manifest, metrics.as_deref_mut())?;
                let result = json!({"kind":"schema-bound","receipts":receipts});
                // Only these existing cross-artifact consumers borrow a manifest later.
                // Other manifests finish their lifecycle at this entry, after replay.
                if matches!(
                    name.as_str(),
                    "pseudonymization-validated"
                        | "claim-settlement-claims"
                        | "claim-settlement-banking"
                ) {
                    verified.insert(name.clone(), (manifest, receipts));
                }
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
            memory_end_entry(&mut observation, &name, memory);
            record(&mut observation, &name, started, "deferred-deployment", 0);
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
            memory_end_entry(&mut observation, &name, memory);
            record(&mut observation, &name, started, "deferred-handoff", 0);
            continue;
        } else {
            return Err(format!("unclassified manifest catalog entry: {name}"));
        };
        memory_end_entry(&mut observation, &name, memory);
        record(
            &mut observation,
            &name,
            started,
            result["kind"].as_str().unwrap_or("unclassified"),
            result["receipts"].as_array().map_or(0, Vec::len),
        );
        output.insert(name, result);
    }
    if let (Some(observation), Some(started)) = (observation.as_deref_mut(), entries_started) {
        observation.entries_ns = started.elapsed().as_nanos();
        observation.retained_manifests = verified.len();
    }
    let memory = memory_start(&observation);
    let finalization = observation.as_ref().map(|_| Instant::now());
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
    // Values are already encoded. Move them into the object instead of serializing
    // every nested receipt into a second JSON tree.
    let output = Value::Object(output.into_iter().collect());
    if let (Some(observation), Some(started)) = (observation.as_deref_mut(), finalization) {
        observation.finalization_ns = started.elapsed().as_nanos();
    }
    memory_end(&mut observation, "finalization", memory);
    let memory = memory_start(&observation);
    let cleanup = observation.as_ref().map(|_| Instant::now());
    drop(verified);
    memory_end(&mut observation, "cleanup", memory);
    if let (Some(observation), Some(started)) = (observation, cleanup) {
        observation.cleanup_ns = started.elapsed().as_nanos();
    }
    Ok(output)
}

#[cfg(test)]
#[path = "../tests/unit/catalog.rs"]
mod tests;
