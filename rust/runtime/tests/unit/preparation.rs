use super::{receipt, validated};
use crate::canonical::json_sha256;
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
    let schema = Schema::from_json_value((*manifest.schema).clone())
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
    let hash = json_sha256(manifest.schema.deref())?;
    crate::replay::check_manifest_with_entities(
        &manifest.cases,
        true,
        None,
        std::collections::BTreeMap::new(),
        crate::entities::EntitySlot::uncached(Some(validator.schema())),
        None,
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
    for name in catalog["entries"]
        .as_object()
        .expect("source catalog entries")
        .keys()
    {
        let value: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(format!(
                "{}/../../.lake/build/{name}-manifest.json",
                env!("CARGO_MANIFEST_DIR")
            ))
            .expect("independent authoring manifest"),
        )
        .expect("manifest JSON");
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
                    None,
                )
            };
            assert_eq!(
                replay_manifest(&manifest),
                original(&manifest.cases),
                "raw receipts: {name}"
            );
            let index = usize::from(manifest.cases.len() > 1);
            let saved = manifest.cases[index].clone();
            manifest.cases[index].entities =
                serde_json::from_value(json!({"invalid":"entity array"})).expect("entity source");
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
            manifest.cases[index] = saved.clone();
            manifest.cases[index].request.action = "Action::\"__changed\"".into();
            assert_eq!(
                replay_manifest(&manifest),
                original(&manifest.cases),
                "fresh raw request: {name}"
            );
            for field in ["context", "principal", "resource"] {
                manifest.cases[index] = saved.clone();
                match field {
                    "context" => manifest.cases[index].request.context = json!({"__changed":true}),
                    "principal" => manifest.cases[index].request.principal = "invalid uid".into(),
                    _ => manifest.cases[index].request.resource = "invalid uid".into(),
                }
                assert_eq!(
                    replay_manifest(&manifest),
                    original(&manifest.cases),
                    "fresh raw {field}: {name}"
                );
            }
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
        assert_eq!(
            metrics.source_policy_loads + metrics.source_policy_reuses,
            metrics.prepared_revisions
        );
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
        manifest.cases[index].entities =
            serde_json::from_value(json!({"invalid":"entity array"})).expect("entity source");
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
        manifest.cases[index] = saved.clone();
        manifest.cases[index].request.action = "Action::\"__changed\"".into();
        assert_eq!(
            replay_validated_manifest(&manifest),
            original_validated_replay(&manifest),
            "fresh action: {name}"
        );
        for field in ["context", "principal", "resource"] {
            manifest.cases[index] = saved.clone();
            match field {
                "context" => manifest.cases[index].request.context = json!({"__changed":true}),
                "principal" => manifest.cases[index].request.principal = "invalid uid".into(),
                _ => manifest.cases[index].request.resource = "invalid uid".into(),
            }
            assert_eq!(
                replay_validated_manifest(&manifest),
                original_validated_replay(&manifest),
                "fresh {field}: {name}"
            );
        }
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
    let prepared = crate::revision::SourcePolicies::new(&other).expect("parse changed body");
    let mut loaded = std::collections::BTreeMap::new();
    loaded.insert(case.revision.clone(), prepared);
    let error = crate::replay::check_manifest_prepared(&[case], true, None, None, loaded)
        .expect_err("source binding must fail before replay");
    assert!(error.contains("prepared policy source mismatch"), "{error}");
}

#[test]
fn entity_reuse_is_scoped_to_invocation_and_actual_schema_and_refusal_retry() {
    let mut original = validated(receipt());
    original.cases[0].entities = serde_json::from_value(
        json!([{"uid":{"type":"User","id":"alice"},"attrs":{},"parents":[]}]),
    )
    .expect("entity source");
    let mut changed = validated(original.cases[0].clone());
    let mut schema_value = changed.schema.deref().clone();
    schema_value[""]["entityTypes"]["User"]["shape"]["attributes"]["age"] =
        json!({"type":"Long","required":true});
    changed.schema = serde_json::from_value(schema_value).unwrap();
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
    next.entities = serde_json::from_value(json!({"invalid":"entities"})).expect("entity source");
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
        serde_json::from_value(json!([{"uid":{"type":"User","id":"bob"},"attrs":{},"parents":[]}]))
            .expect("entity source");
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
    invalid.entities = serde_json::from_value(json!({"bad":"entities"})).expect("entity source");
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

#[test]
fn policy_body_preparation_shares_only_complete_source_within_one_invocation() {
    let first = receipt();
    let mut same = first.clone();
    same.name = "same-body".into();
    same.revision = "same-body".into();
    let mut changed = first.clone();
    changed.name = "changed-body".into();
    changed.revision = "changed-body".into();
    let mut artifact = changed.policies.deref().clone();
    artifact["staticPolicies"]["base"]["effect"] = json!("forbid");
    changed.policies = serde_json::from_value(artifact).expect("different body at same policy ID");
    changed.expected = "deny".into();
    let manifest = Manifest {
        cases: vec![first, same, changed],
    };
    let original = || {
        crate::replay::check_manifest_with_entities(
            &manifest.cases,
            true,
            None,
            std::collections::BTreeMap::new(),
            crate::entities::EntitySlot::uncached(None),
            None,
        )
    };
    for _ in 0..2 {
        let mut metrics = crate::ReplayMetrics::default();
        let actual =
            crate::replay_manifest_measured(&manifest, &mut metrics).expect("shared preparation");
        assert_eq!(
            actual,
            original().expect("independent uncached normalization")
        );
        assert_eq!(metrics.policy_body_normalizations, 2);
        assert_eq!(metrics.policy_body_reuses, 0);
        assert_eq!(metrics.revision_syntax_reuses, 1);
        assert_eq!(metrics.policy_body_slot_peak, 2);
        assert_eq!(metrics.prepared_revisions, 3);
        assert_eq!(metrics.source_policy_loads, 2);
        assert_eq!(metrics.source_policy_reuses, 1);
        assert_eq!(metrics.authorization_calls, 6);
    }
    let mut conflict = manifest;
    conflict.cases[2].revision = conflict.cases[0].revision.clone();
    let error = replay_manifest(&conflict).expect_err("same revision cannot hide changed body");
    assert!(error.contains("conflicting revision output"), "{error}");
}

#[test]
fn shared_schema_retires_and_never_reuses_validation_or_requests() {
    let manifest = validated(receipt());
    let source = || manifest.schema.clone();
    let mut owner = crate::SchemaPreparation::from_sources([source(), source()]).unwrap();
    let mut metrics = crate::ReplayMetrics::default();
    assert_eq!(
        owner.replay(&manifest, Some(&mut metrics)),
        original_validated_replay(&manifest)
    );
    let mut changed = validated(receipt());
    let mut schema_value = changed.schema.deref().clone();
    schema_value[""]["entityTypes"]["Extra"] = json!({"shape":{"type":"Record","attributes":{}}});
    changed.schema = serde_json::from_value(schema_value).unwrap();
    assert_eq!(
        owner.replay(&changed, Some(&mut metrics)),
        original_validated_replay(&changed)
    );
    assert_eq!((metrics.schema_parse_calls, metrics.schema_reuses), (2, 0));
    let mut invalid = validated(receipt());
    invalid.cases[0].request.context = json!({"unlisted":true});
    assert_eq!(
        owner.replay(&invalid, Some(&mut metrics)),
        original_validated_replay(&invalid)
    );
    assert_eq!((metrics.schema_parse_calls, metrics.schema_reuses), (2, 1));
    owner.replay(&manifest, Some(&mut metrics)).unwrap();
    assert_eq!(
        metrics.schema_parse_calls, 3,
        "last planned use retires SDK state"
    );
    assert_eq!(
        metrics.policy_validation_calls, 4,
        "every replay validates policies afresh"
    );
    let mut policy = validated(receipt());
    let mut value = policy.cases[0].policies.deref().clone();
    value["staticPolicies"]["base"]["conditions"] =
        json!([{"kind":"when","body":{".":{"left":{"Var":"principal"},"attr":"missing"}}}]);
    policy.cases[0].policies = serde_json::from_value(value).unwrap();
    assert_eq!(
        owner.replay(&policy, None),
        original_validated_replay(&policy)
    );
}

#[test]
fn wire_schema_preparation_preserves_original_sdk_rejection_and_invocation_counts() {
    let mut sources = vec![validated(receipt()).schema];
    for value in [
        json!([]),
        json!({"invalid":false}),
        json!({"": {"entityTypes": {"Bad": {"shape": {"type": "Unknown"}}}}}),
        json!({"雪": {"entityTypes": {}, "actions": {}}}),
    ] {
        sources.push(serde_json::from_value(value).unwrap());
    }
    for source in sources {
        let expected = cedar_policy::Schema::from_json_value((*source).clone())
            .map(|_| ())
            .map_err(|error| format!("Cedar schema: {error}"));
        let mut stats = crate::ReplayMetrics::default();
        let actual =
            crate::schema_preparation::PreparedSchema::parse(&source, Some(&mut stats)).map(|_| ());
        assert_eq!(actual, expected);
        assert_eq!(stats.schema_parse_calls, 1);
        assert_eq!(
            stats.schema_diagnostic_reparses,
            usize::from(expected.is_err())
        );
    }
}
