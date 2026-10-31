use super::replay;
use serde_json::json;
fn fixture() -> serde_json::Value {
    let inline = json!({"raw":{"cases":[{"name":"allow-all","revision":"published","policy_ids":["base"],
        "policies":{"staticPolicies":{"base":{"effect":"permit","principal":{"op":"All"},"action":{"op":"All"},"resource":{"op":"All"},"conditions":[]}},"templates":{},"templateLinks":[]},
        "entities":[],"request":{"principal":"User::\"alice\"","action":"Action::\"view\"","resource":"Document::\"one\"","context":{}},
        "expected":"allow","expected_reasons":["base"],"expected_error_policies":[]}]}});
    let mut row = inline["raw"]["cases"][0].clone();
    let policies = row.as_object_mut().unwrap().remove("policies").unwrap();
    let entities = row.as_object_mut().unwrap().remove("entities").unwrap();
    row["policy_ref"] = json!(0);
    row["entities_ref"] = json!(0);
    json!({"format_version":2,"sources":{"policies":[policies],"entities":[entities],"schemas":[]},"entries":{"raw":{"manifest_kind":"raw","revision_sources":{"published":0},"cases":[row]}}})
}
#[test]
fn complete_cedar_receipts_are_returned_and_changed_expectations_fail() {
    let mut input = fixture();
    let output = replay(&input.to_string()).expect("official Cedar replay");
    assert_eq!(output["raw"]["receipts"][0]["decision"], "allow");
    assert_eq!(output["raw"]["receipts"][0]["error_free_allow"], true);
    input["entries"]["raw"]["cases"][0]["expected"] = json!("deny");
    assert!(replay(&input.to_string()).is_err());
}
#[test]
fn unclassified_and_empty_catalogs_do_not_silently_pass() {
    assert!(replay("{}").is_err());
    for entries in [
        json!({}),
        json!({"unknown":{"payload":true}}),
        json!({"raw":{"manifest_kind":"raw","revision_sources":{},"cases":[]}}),
        json!({"pseudonymization-tabular":{}}),
        json!({"pseudonymization-deployable":[]}),
        json!({"claim-settlement-handoff":[]}),
    ] {
        let mut input = fixture();
        input["entries"] = entries;
        assert!(replay(&input.to_string()).is_err());
    }
}

// This test consumes the real Lean output instead of a second Rust scenario catalog.
// The official gate emits that artifact before explicitly running this test.
#[test]
#[ignore = "requires the official Lean catalog; run just check-functional-catalog"]
fn emitted_catalog_rejects_cross_artifact_tampering() {
    let input = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../.lake/build/functional-catalog.json"
    ))
    .expect("official Lean catalog must be emitted first");
    let catalog: serde_json::Value = serde_json::from_str(&input).expect("catalog JSON");
    let output = replay(&input).expect("unmodified complete catalog");
    let mut stages = crate::catalog_observation::CatalogObservation::default();
    let mut metrics = cedar_poo_runtime::ReplayMetrics::default();
    let profiled = super::replay_observed(&input, Some(&mut metrics), Some(&mut stages))
        .expect("observed complete catalog");
    assert_eq!(
        profiled, output,
        "observation and early retirement preserve every receipt"
    );
    assert_eq!(stages.entries.len(), 51);
    assert_eq!(stages.retained_manifests, 3);
    assert_eq!(metrics.authorization_calls, 2560);
    assert_eq!(metrics.uid_parse_calls + metrics.uid_reuses, 3840);
    assert!(metrics.uid_reuses > 0);
    assert!(metrics.uid_slot_peak <= metrics.uid_parse_calls);
    assert_eq!(metrics.policy_body_normalizations, 335);
    assert_eq!(metrics.policy_body_reuses, 494);
    assert_eq!(
        (
            metrics.source_policy_loads,
            metrics.source_policy_reuses,
            metrics.revision_syntax_reuses
        ),
        (194, 27, 27)
    );
    assert_eq!(
        (
            metrics.schema_parse_calls,
            metrics.schema_reuses,
            metrics.policy_validation_calls
        ),
        (21, 2, 112)
    );
    assert_eq!(
        (metrics.entity_hash_calls, metrics.entity_hash_reuses),
        (53, 1227)
    );
    assert_eq!(metrics.policy_body_slot_peak, 21);

    assert_eq!(
        output.as_object().expect("catalog receipt object").len(),
        51
    );
    let financial_entries = json!({
        "claim-settlement-claims": catalog["entries"]["claim-settlement-claims"],
        "claim-settlement-banking": catalog["entries"]["claim-settlement-banking"],
        "claim-settlement-handoff": catalog["entries"]["claim-settlement-handoff"]
    });
    let mut financial = catalog.clone();
    financial["entries"] = financial_entries;
    let reject = |mutated: serde_json::Value, expected: &str| {
        let error = replay(&mutated.to_string()).expect_err("tampered artifact must refuse");
        assert!(
            error.contains(expected),
            "expected {expected:?}, got {error:?}"
        );
    };
    let mut changed = financial.clone();
    changed["entries"]["claim-settlement-handoff"][0]["scope"]["claimDigest"] = json!("forged");
    reject(changed, "claim-settlement Lean/Rust mismatch: ready");
    let mut changed = financial.clone();
    changed["entries"]["claim-settlement-handoff"][0]["scope"]["targetActor"] =
        json!("AgentCore::OAuthUser::\"other\"");
    reject(changed, "handoff case root/actor mismatch");
    let mut changed = financial.clone();
    changed["entries"]["claim-settlement-handoff"][0]["claims"][0] = json!("claims-eu-claims-0");
    reject(changed, "claims scenario/index binding mismatch");
    let mut changed = financial.clone();
    changed["entries"]["claim-settlement-handoff"][0]["banking"][0]["phase"] =
        json!("debit-source");
    reject(changed, "bank phase/LOB/action/origin binding mismatch");
    let mut changed = financial;
    changed["entries"]["claim-settlement-handoff"][0]["banking"][0]["required"] = json!([
        "jwtAtLob",
        "m2mGatewayToLob",
        "userJwtAgentToGateway",
        "cedarAtGateway",
        "retailDataPlane"
    ]);
    reject(changed, "banking requirement projection mismatch");
    let mut changed = catalog.clone();
    let original = catalog["entries"]["pseudonymization-deployable"][0]["policy_ref"]
        .as_u64()
        .unwrap() as usize;
    let wrong = catalog["sources"]["policies"]
        .as_array()
        .unwrap()
        .iter()
        .position(|value| value != &catalog["sources"]["policies"][original])
        .unwrap();
    changed["entries"]["pseudonymization-deployable"][0]["policy_ref"] = json!(wrong);
    reject(
        changed,
        "deployment policy artifact differs from schema-bound source",
    );
    let mut changed = catalog;
    changed["entries"]["pseudonymization-deployable"][0]["root"] = json!("Base");
    reject(changed, "invalid or duplicate deployment root");
}

#[test]
fn measured_catalog_preserves_complete_output_and_refuses_the_same_invalid_input() {
    let input = fixture().to_string();
    let mut metrics = cedar_poo_runtime::ReplayMetrics::default();
    let measured = super::replay_observed(&input, Some(&mut metrics), None).expect("measured");
    assert_eq!(measured, replay(&input).expect("ordinary"));
    assert_eq!(metrics.authorization_calls, 2);
    assert_eq!(metrics.prepared_revisions, 1);
    assert_eq!(
        super::replay_observed("{}", Some(&mut metrics), None).expect_err("empty measured catalog"),
        replay("{}").expect_err("empty ordinary catalog")
    );
}

#[test]
fn source_reference_controls_reject_duplicate_wire_fields() {
    let ordinary = fixture().to_string();
    let duplicated = ordinary.replace(
        "\"name\":\"allow-all\"",
        "\"name\":\"ignored\",\"name\":\"allow-all\"",
    );
    assert_ne!(
        ordinary, duplicated,
        "duplicate-field control must mutate input"
    );
    replay(&ordinary).expect("ordinary source catalog");
    assert!(replay(&duplicated).unwrap_err().contains("duplicate field"));
}

#[test]
fn complete_parse_errors_and_late_schema_inputs_keep_original_precedence() {
    let input = r#"{"a":{"cases":[]},"z":{"cases":[],"schema":null},"zz":1e400}"#;
    let error =
        serde_json::from_str::<std::collections::BTreeMap<String, serde_json::Value>>(input)
            .unwrap_err()
            .to_string();
    assert_eq!(
        replay(input).unwrap_err(),
        error,
        "full input syntax before any domain error"
    );
    assert!(
        replay(r#"{"a":{"cases":[]},"z":{"cases":[],"schema":null}}"#)
            .unwrap_err()
            .contains("unknown field")
    );
}

#[test]
fn later_missing_schema_ref_does_not_hide_earlier_sdk_workflow_error() {
    let mut input = fixture();
    input["entries"] = json!({"a":{"cases":[],"manifest_kind":"raw","revision_sources":{}},"z":{"cases":[],"manifest_kind":"schema-bound","revision_sources":{},"schema_ref":999}});
    assert_eq!(
        replay(&input.to_string()).unwrap_err(),
        "manifest has no cases"
    );
}

#[test]
fn source_envelope_version_duplicate_names_and_unknown_roles_are_refused() {
    let mut input = fixture();
    input["format_version"] = json!(1);
    assert!(
        replay(&input.to_string())
            .unwrap_err()
            .contains("unsupported catalog format")
    );
    input = fixture();
    input["sources"]["extra_role"] = json!([]);
    assert!(
        replay(&input.to_string())
            .unwrap_err()
            .contains("unknown field")
    );
    let duplicate = fixture()
        .to_string()
        .replace("\"raw\":", "\"raw\":{},\"raw\":");
    assert!(
        replay(&duplicate)
            .unwrap_err()
            .contains("duplicate catalog entry")
    );
    let duplicate = fixture().to_string().replace(
        "\"format_version\":2",
        "\"format_version\":2,\"format_version\":2",
    );
    assert!(replay(&duplicate).unwrap_err().contains("duplicate field"));
}
