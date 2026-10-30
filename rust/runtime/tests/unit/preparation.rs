use super::{receipt, validated};
use crate::bridge::json_sha256;
use crate::{
    Case, Manifest, ValidatedManifest, load_policy_set, replay_manifest, replay_validated_manifest,
};
use serde_json::json;
use std::ops::Deref;

#[test]
fn schema_preparation_reuses_policies_and_preserves_validation_before_request_errors() {
    let mut manifest = validated(receipt());
    let mut next = receipt();
    next.name = "later".into();
    manifest.cases.push(next);
    let mut metrics = crate::ReplayMetrics::default();
    crate::replay_validated_manifest_measured(&manifest, &mut metrics).expect("same revision");
    assert_eq!(metrics.source_policy_loads, 1);
    assert_eq!(metrics.prepared_revisions, 1);
    assert_eq!(metrics.authorization_calls, 4);
    manifest.cases[0].request.context = json!({"unlisted":true});
    manifest.cases[1].revision = "later".into();
    manifest.cases[1].policies = serde_json::from_value(json!({
        "staticPolicies":{"base":{"effect":"permit","principal":{"op":"All"},"action":{"op":"All"},
        "resource":{"op":"All"},"conditions":[{"kind":"when","body":{".":{"left":{"Var":"principal"},"attr":"missing"}}}]}},
        "templates":{},"templateLinks":[]})).expect("wire AST");
    // Invalid policy input must win over an earlier invalid request, as before.
    let error = replay_validated_manifest(&manifest).expect_err("invalid later policy");
    assert!(
        error.contains("strict policy validation"),
        "validation must precede request preparation: {error}"
    );
}

// Independent pre-optimization schema workflow, retained only as a test oracle.
fn original_validated_replay(
    manifest: &ValidatedManifest,
) -> Result<Vec<crate::SchemaBoundReceipt>, String> {
    use cedar_policy::{Schema, ValidationMode, Validator};
    let schema = Schema::from_json_value(manifest.schema.clone())
        .map_err(|e| format!("Cedar schema: {e}"))?;
    let validator = Validator::new(schema);
    let mut roots = std::collections::BTreeSet::new();
    for case in &manifest.cases {
        if roots.insert(&case.revision) {
            let policies = load_policy_set(&case.policies)?;
            let result = validator.validate(&policies, ValidationMode::Strict);
            if !result.validation_passed() {
                return Err(format!(
                    "{}: Cedar strict policy validation failed: {result:?}",
                    case.revision
                ));
            }
        }
    }
    let hash = json_sha256(&manifest.schema)?;
    crate::replay::check_manifest_with_entities(
        &manifest.cases,
        true,
        None,
        std::collections::BTreeMap::new(),
        crate::entities::EntitySlot::uncached(Some(validator.schema())),
    )
    .map(|rows| {
        rows.into_iter()
            .map(|replay| crate::SchemaBoundReceipt {
                schema_sha256: hash.clone(),
                replay,
            })
            .collect()
    })
}

#[test]
#[ignore = "requires official emitted catalog; run just check-functional-catalog"]
fn prepared_catalog_matches_original_workflows() {
    let input = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../.lake/build/functional-catalog.json"
    ))
    .expect("official Lean catalog");
    let catalog: std::collections::BTreeMap<String, serde_json::Value> =
        serde_json::from_str(&input).expect("catalog");
    let mut checked = 0;
    let mut raw_checked = 0;
    for (name, value) in catalog {
        if value.get("cases").is_none() {
            continue;
        }
        // Independent legacy JSON -> AST normalization, before the optimized
        // replay/oracle share their checked-revision owner.
        let cases: Vec<Case> = serde_json::from_value(value["cases"].clone()).expect("cases");
        let mut revisions = std::collections::BTreeSet::new();
        for case in &cases {
            if revisions.insert(&case.revision) {
                super::assert_legacy_revision_bodies(case);
            }
        }
        if value.get("schema").is_none() {
            let mut manifest: Manifest = serde_json::from_value(value).expect("raw manifest");
            let original = |cases: &[Case]| {
                crate::replay::check_manifest_with_entities(
                    cases,
                    true,
                    None,
                    std::collections::BTreeMap::new(),
                    crate::entities::EntitySlot::uncached(None),
                )
            };
            assert_eq!(
                replay_manifest(&manifest),
                original(&manifest.cases),
                "raw receipts: {name}"
            );
            let index = usize::from(manifest.cases.len() > 1);
            let saved = manifest.cases[index].clone();
            manifest.cases[index].entities = json!({"invalid":"entity array"});
            manifest.cases[index].request.action = "invalid uid".into();
            assert_eq!(
                replay_manifest(&manifest).expect_err("entities before action"),
                original(&manifest.cases).expect_err("reference raw entities"),
                "{name}"
            );
            manifest.cases[index]
                .policy_ids
                .push("invalid-policy-id".into());
            assert_eq!(
                replay_manifest(&manifest).expect_err("ids before entities"),
                original(&manifest.cases).expect_err("reference raw ids"),
                "{name}"
            );
            manifest.cases[index] = saved;
            manifest.cases[index].request.action = "Action::\"__changed\"".into();
            assert_eq!(
                replay_manifest(&manifest),
                original(&manifest.cases),
                "fresh raw request: {name}"
            );
            raw_checked += 1;
            continue;
        }
        let mut manifest: ValidatedManifest =
            serde_json::from_value(value).expect("validated manifest");
        let expected = original_validated_replay(&manifest).expect("original workflow");
        let mut metrics = crate::ReplayMetrics::default();
        let actual = crate::replay_validated_manifest_measured(&manifest, &mut metrics)
            .expect("prepared workflow");
        assert_eq!(actual, expected, "complete receipts: {name}");
        assert_eq!(metrics.source_policy_loads, metrics.prepared_revisions);
        let original_cases = manifest.cases.clone();
        manifest.cases[0].expected = if manifest.cases[0].expected == "allow" {
            "deny"
        } else {
            "allow"
        }
        .into();
        assert_eq!(
            replay_validated_manifest(&manifest).expect_err("prepared refusal"),
            original_validated_replay(&manifest).expect_err("original refusal"),
            "{name}"
        );
        manifest.cases = original_cases;
        let index = usize::from(manifest.cases.len() > 1);
        let saved = manifest.cases[index].clone();
        manifest.cases[index].entities = json!({"invalid":"entity array"});
        manifest.cases[index].request.action = "invalid uid".into();
        assert_eq!(
            replay_validated_manifest(&manifest).expect_err("entities before action"),
            original_validated_replay(&manifest).expect_err("reference entities"),
            "{name}"
        );
        manifest.cases[index]
            .policy_ids
            .push("invalid-policy-id".into());
        assert_eq!(
            replay_validated_manifest(&manifest).expect_err("ids before entities"),
            original_validated_replay(&manifest).expect_err("reference ids"),
            "{name}"
        );
        manifest.cases[index] = saved;
        manifest.cases[index].request.action = "Action::\"__changed\"".into();
        assert_eq!(
            replay_validated_manifest(&manifest),
            original_validated_replay(&manifest),
            "fresh action: {name}"
        );
        checked += 1;
    }
    assert_eq!(checked, 23, "schema-bearing catalog coverage changed");
    assert_eq!(raw_checked, 24, "raw catalog coverage changed");
}

#[test]
fn prepared_source_cannot_be_rebound_to_same_named_different_policy_body() {
    let case = receipt();
    let mut other = receipt();
    let mut wire = other.policies.deref().clone();
    wire["staticPolicies"]["base"]["effect"] = json!("forbid");
    other.policies = serde_json::from_value(wire).expect("changed source");
    let prepared = crate::bridge::SourcePolicies::new(&other).expect("parse changed body");
    let mut loaded = std::collections::BTreeMap::new();
    loaded.insert(case.revision.clone(), prepared);
    let error = crate::replay::check_manifest_prepared(&[case], true, None, None, loaded)
        .expect_err("source binding must fail before replay");
    assert!(error.contains("prepared policy source mismatch"), "{error}");
}

#[test]
fn entity_reuse_is_scoped_to_invocation_and_actual_schema_and_refusal_retry() {
    let mut original = validated(receipt());
    original.cases[0].entities =
        json!([{"uid":{"type":"User","id":"alice"},"attrs":{},"parents":[]}]);
    let mut changed = validated(original.cases[0].clone());
    changed.schema[""]["entityTypes"]["User"]["shape"]["attributes"]["age"] =
        json!({"type":"Long","required":true});
    let mut stats = crate::ReplayMetrics::default();
    crate::replay_validated_manifest_measured(&original, &mut stats).expect("original schema");
    let error = crate::replay_validated_manifest_measured(&changed, &mut stats)
        .expect_err("same source must be checked under changed schema");
    assert!(error.contains("Cedar schema entities"), "{error}");
    crate::replay_validated_manifest_measured(&original, &mut stats)
        .expect("successful independent retry");
    assert_eq!(stats.entity_parse_calls, 3);
    assert_eq!(stats.entity_reuses, 0);
}

#[test]
fn entity_replacement_and_simultaneous_faults_preserve_original_error_order() {
    let mut manifest = validated(receipt());
    let mut next = receipt();
    next.name = "second".into();
    next.entities = json!({"invalid":"entities"});
    next.policy_ids = vec!["wrong".into()];
    manifest.cases.push(next);
    assert_eq!(
        replay_validated_manifest(&manifest).expect_err("two faults"),
        original_validated_replay(&manifest).expect_err("reference faults")
    );
    manifest.cases[1].policy_ids = vec!["base".into()];
    assert_eq!(
        replay_validated_manifest(&manifest).expect_err("changed invalid entities"),
        original_validated_replay(&manifest).expect_err("reference changed entities")
    );
    manifest.cases[1].entities =
        json!([{"uid":{"type":"User","id":"bob"},"attrs":{},"parents":[]}]);
    let mut stats = crate::ReplayMetrics::default();
    let actual =
        crate::replay_validated_manifest_measured(&manifest, &mut stats).expect("replacement");
    assert_eq!(
        actual,
        original_validated_replay(&manifest).expect("reference replacement")
    );
    assert_eq!(
        (
            stats.entity_parse_calls,
            stats.entity_reuses,
            stats.entity_replacements,
            stats.entity_slot_peak
        ),
        (2, 0, 1, 1)
    );
}

#[test]
fn direct_source_batch_retains_error_prefixes_and_matches_fresh_preparation() {
    let valid = receipt();
    let mut invalid = valid.clone();
    invalid.name = "invalid".into();
    invalid.entities = json!({"bad":"entities"});
    let mut two_faults = invalid.clone();
    two_faults.name = "two-faults".into();
    two_faults.policy_ids.push("wrong".into());
    let policies = load_policy_set(&valid.policies).expect("policies");
    let cases = [valid, invalid, two_faults];
    let mut shared = crate::entities::EntitySlot::new(None);
    for case in &cases {
        let actual = crate::bridge::check_direct_case(case, &policies, &mut shared);
        let mut fresh = crate::entities::EntitySlot::uncached(None);
        let expected = crate::bridge::check_direct_case(case, &policies, &mut fresh);
        assert_eq!(actual, expected);
        match case.name.as_str() {
            "invalid" => assert!(actual.expect_err("entities").starts_with("Cedar entities:")),
            "two-faults" => assert_eq!(
                actual.expect_err("IDs before entities"),
                "direct policy count differs"
            ),
            _ => actual.expect("valid direct input"),
        }
    }
}
