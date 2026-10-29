use super::replay;
use serde_json::json;
fn fixture() -> serde_json::Value {
    json!({"raw":{"cases":[{"name":"allow-all","revision":"published","policy_ids":["base"],
        "policies":{"staticPolicies":{"base":{"effect":"permit","principal":{"op":"All"},"action":{"op":"All"},"resource":{"op":"All"},"conditions":[]}},"templates":{},"templateLinks":[]},
        "entities":[],"request":{"principal":"User::\"alice\"","action":"Action::\"view\"","resource":"Document::\"one\"","context":{}},
        "expected":"allow","expected_reasons":["base"],"expected_error_policies":[]}]}})
}
#[test]
fn complete_cedar_receipts_are_returned_and_changed_expectations_fail() {
    let mut input = fixture();
    let output = replay(&input.to_string()).expect("official Cedar replay");
    assert_eq!(output["raw"]["receipts"][0]["decision"], "allow");
    assert_eq!(output["raw"]["receipts"][0]["error_free_allow"], true);
    input["raw"]["cases"][0]["expected"] = json!("deny");
    assert!(replay(&input.to_string()).is_err());
}
#[test]
fn unclassified_and_empty_catalogs_do_not_silently_pass() {
    assert!(replay("{}").is_err());
    assert!(replay(r#"{"unknown":{"payload":true}}"#).is_err());
    assert!(replay(r#"{"raw":{"cases":[]}}"#).is_err());
    assert!(replay(r#"{"pseudonymization-tabular":{}}"#).is_err());
    assert!(replay(r#"{"pseudonymization-deployable":[]}"#).is_err());
    assert!(replay(r#"{"claim-settlement-handoff":[]}"#).is_err());
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
    assert_eq!(
        output.as_object().expect("catalog receipt object").len(),
        51
    );
    let financial = json!({
        "claim-settlement-claims": catalog["claim-settlement-claims"],
        "claim-settlement-banking": catalog["claim-settlement-banking"],
        "claim-settlement-handoff": catalog["claim-settlement-handoff"]
    });
    let reject = |mutated: serde_json::Value, expected: &str| {
        let error = replay(&mutated.to_string()).expect_err("tampered artifact must refuse");
        assert!(
            error.contains(expected),
            "expected {expected:?}, got {error:?}"
        );
    };
    let mut changed = financial.clone();
    changed["claim-settlement-handoff"][0]["scope"]["claimDigest"] = json!("forged");
    reject(changed, "claim-settlement Lean/Rust mismatch: ready");
    let mut changed = financial.clone();
    changed["claim-settlement-handoff"][0]["scope"]["targetActor"] =
        json!("AgentCore::OAuthUser::\"other\"");
    reject(changed, "handoff case root/actor mismatch");
    let mut changed = financial.clone();
    changed["claim-settlement-handoff"][0]["claims"][0] = json!("claims-eu-claims-0");
    reject(changed, "claims scenario/index binding mismatch");
    let mut changed = financial.clone();
    changed["claim-settlement-handoff"][0]["banking"][0]["phase"] = json!("debit-source");
    reject(changed, "bank phase/LOB/action/origin binding mismatch");
    let mut changed = financial;
    changed["claim-settlement-handoff"][0]["banking"][0]["required"] = json!([
        "jwtAtLob",
        "m2mGatewayToLob",
        "userJwtAgentToGateway",
        "cedarAtGateway",
        "retailDataPlane"
    ]);
    reject(changed, "banking requirement projection mismatch");
    let mut changed = catalog;
    changed["pseudonymization-deployable"][0]["root"] = json!("Base");
    reject(changed, "invalid or duplicate deployment root");
}

#[test]
fn measured_catalog_preserves_complete_output_and_refuses_the_same_invalid_input() {
    let input = fixture().to_string();
    let mut metrics = cedar_poo_runtime::ReplayMetrics::default();
    let measured = super::replay_measured(&input, &mut metrics).expect("measured");
    assert_eq!(measured, replay(&input).expect("ordinary"));
    assert_eq!(metrics.authorization_calls, 2);
    assert_eq!(metrics.prepared_revisions, 1);
    assert_eq!(
        super::replay_measured("{}", &mut metrics).expect_err("empty measured catalog"),
        replay("{}").expect_err("empty ordinary catalog")
    );
}
