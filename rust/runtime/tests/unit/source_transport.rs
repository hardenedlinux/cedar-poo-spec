use super::CatalogSources;
use cedar_poo_core::JsonSourceIdentity;
use serde_json::{Value, json};
use std::ops::Deref;
fn source() -> Value {
    json!({"staticPolicies":{"base":{"effect":"permit","principal":{"op":"All"},"action":{"op":"All"},"resource":{"op":"All"},"conditions":[]}},"templates":{},"templateLinks":[]})
}
fn registry() -> Value {
    json!({"policies":[source()],"entities":[[]],"schemas":[]})
}
fn manifest() -> Value {
    json!({"manifest_kind":"raw","revision_sources":{"published":0},"cases":[{"name":"one","revision":"published","policy_ids":["base"],"policy_ref":0,"entities_ref":0,"request":{"principal":"User::\"alice\"","action":"Action::\"view\"","resource":"Document::\"one\"","context":{}},"expected":"allow","expected_reasons":["base"],"expected_error_policies":[]}]})
}
#[test]
fn resolved_cases_share_actual_sources_but_both_authorizers_execute() {
    let sources: CatalogSources = serde_json::from_value(registry()).unwrap();
    sources.check_unique().unwrap();
    let mut raw = manifest();
    let mut second = raw["cases"][0].clone();
    second["name"] = json!("two");
    raw["cases"].as_array_mut().unwrap().push(second);
    let decoded = sources.manifest(&raw.to_string()).unwrap();
    assert!(std::ptr::eq(
        decoded.cases[0].policies.deref(),
        decoded.cases[1].policies.deref()
    ));
    assert!(std::ptr::eq(
        decoded.cases[0].entities.deref(),
        decoded.cases[1].entities.deref()
    ));
    let mut metrics = crate::ReplayMetrics::default();
    crate::replay_manifest_measured(&decoded, &mut metrics).unwrap();
    assert_eq!(metrics.authorization_calls, 4);
    raw["cases"][1]["request"]["context"] = json!([]);
    assert!(crate::replay_manifest(&sources.manifest(&raw.to_string()).unwrap()).is_err());
}
#[test]
fn wrong_missing_stale_duplicate_and_ambiguous_references_are_refused() {
    let sources: CatalogSources = serde_json::from_value(registry()).unwrap();
    for key in ["policy_ref", "entities_ref"] {
        let mut raw = manifest();
        raw["cases"][0][key] = json!(999);
        assert!(sources.manifest(&raw.to_string()).is_err());
        raw["cases"][0][key] = json!({"kind":"schema","index":0});
        assert!(sources.manifest(&raw.to_string()).is_err());
    }
    let mut raw = manifest();
    raw["revision_sources"] = json!({});
    assert!(
        sources
            .manifest(&raw.to_string())
            .unwrap_err()
            .contains("binding mismatch")
    );
    let duplicate = manifest()
        .to_string()
        .replace("\"published\":0", "\"published\":0,\"published\":0");
    assert!(
        sources
            .manifest(&duplicate)
            .unwrap_err()
            .contains("duplicate revision binding")
    );
    raw = manifest();
    raw["cases"][0]["policies"] = source();
    assert!(
        sources
            .manifest(&raw.to_string())
            .unwrap_err()
            .contains("unknown field")
    );
    let mut reg = registry();
    reg["policies"].as_array_mut().unwrap().push(source());
    assert!(
        serde_json::from_value::<CatalogSources>(reg)
            .unwrap()
            .check_unique()
            .unwrap_err()
            .contains("duplicate source")
    );
}
#[test]
fn table_resolution_never_establishes_policy_admission() {
    let mut reg = registry();
    reg["policies"][0] = json!({"invalid":"policy"});
    let sources: CatalogSources = serde_json::from_value(reg).unwrap();
    sources.check_unique().unwrap();
    let decoded = sources.manifest(&manifest().to_string()).unwrap();
    assert!(crate::replay_manifest(&decoded).is_err());
    let mut raw = manifest();
    raw["schema_ref"] = json!(999);
    raw["manifest_kind"] = json!("schema-bound");
    assert!(
        sources
            .validated_manifest(&raw.to_string())
            .unwrap_err()
            .contains("schema reference")
    );
}

#[test]
fn schema_reference_cannot_be_stripped_or_merged_into_raw_manifest() {
    let sources: CatalogSources = serde_json::from_value(registry()).unwrap();
    let mut raw = manifest();
    raw["manifest_kind"] = json!("schema-bound");
    assert!(
        sources
            .validated_manifest(&raw.to_string())
            .unwrap_err()
            .contains("schema_ref")
    );
    assert!(
        sources
            .manifest(&raw.to_string())
            .unwrap_err()
            .contains("unknown variant")
    );
    raw["schema_ref"] = json!(0);
    assert!(
        sources
            .validated_manifest(&raw.to_string())
            .unwrap_err()
            .contains("out of bounds")
    );
}

#[test]
fn entity_uniqueness_remains_exact_even_when_all_fingerprints_collide() {
    let values = [
        json!([]),
        json!({"x":0.0}),
        json!({"x":-0.0}),
        json!({"x":1}),
        json!({"x":true}),
        json!({"x":"雪"}),
        json!([{"x":1},{"x":2}]),
    ];
    for a in &values {
        for b in &values {
            let sources = [
                serde_json::from_value(a.clone()).unwrap(),
                serde_json::from_value(b.clone()).unwrap(),
            ];
            assert_eq!(
                super::unique_entities_by(&sources, |_| 0).is_err(),
                a.encode_source().unwrap() == b.encode_source().unwrap()
            );
        }
    }
}
