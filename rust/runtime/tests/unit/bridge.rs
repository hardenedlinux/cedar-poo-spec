use crate::canonical::json_sha256;
use crate::schema::{
    SchemaEvolutionBundle, ValidatedManifest, render_validated_policy_sources,
    replay_schema_only_revision, replay_validated_manifest, verify_schema_only_revision,
    verify_validated_replay_receipts,
};
use crate::{
    Case, Manifest, check_direct_sources, check_manifest, check_template_source, load_policy_set,
    load_template_source, render_artifacts, render_identified_policy_sources, replay_manifest,
    verify_replay_receipts,
};
use serde_json::json;
use std::ops::Deref;

fn receipt() -> Case {
    serde_json::from_value(json!({
            "name": "allow-all",
            "revision": "published",
            "policy_ids": ["base"],
        "policies": {
            "staticPolicies": {
                "base": {
                    "effect": "permit",
                    "principal": { "op": "All" },
                    "action": { "op": "All" },
                    "resource": { "op": "All" },
                    "conditions": []
                }
            },
            "templates": {},
            "templateLinks": []
        },
        "entities": [],
        "request": {
            "principal": "User::\"alice\"",
            "action": "Action::\"view\"",
            "resource": "Document::\"one\"",
            "context": {}
        },
        "expected": "allow",
        "expected_reasons": ["base"],
        "expected_error_policies": []
    }))
    .expect("valid local receipt")
}

#[test]
fn identified_sources_preserve_each_cedar_policy_id_and_body() {
    let mut case = receipt();
    let mut artifact = case.policies.deref().clone();
    artifact["staticPolicies"]["second"] = artifact["staticPolicies"]["base"].clone();
    case.policies = serde_json::from_value(artifact).expect("two-policy artifact");

    let sources = render_identified_policy_sources(&case.policies)
        .expect("render individually identified policies");
    assert_eq!(
        sources.keys().map(String::as_str).collect::<Vec<_>>(),
        ["base", "second"]
    );
    let loaded = load_policy_set(&case.policies).expect("Cedar policy set");
    for policy in loaded.policies() {
        let source = &sources[&policy.id().to_string()];
        let reparsed = cedar_policy::Policy::parse(Some(policy.id().clone()), source)
            .expect("explicit-ID Cedar source");
        assert_eq!(reparsed.id(), policy.id());
        assert_eq!(reparsed.to_json().unwrap(), policy.to_json().unwrap());
    }
}

#[test]
fn validated_sources_bind_one_schema_and_entity_snapshot_for_permit_and_forbid() {
    let mut allow = receipt();
    let mut artifact = allow.policies.deref().clone();
    artifact["staticPolicies"]["blocked"] = json!({
        "effect": "forbid",
        "principal": {"op": "All"},
        "action": {"op": "All"},
        "resource": {"op": "All"},
        "conditions": [{"kind": "when", "body": {
            ".": {"left": {"Var": "context"}, "attr": "blocked"}
        }}]
    });
    allow.policies = serde_json::from_value(artifact).unwrap();
    allow.policy_ids = vec!["base".into(), "blocked".into()];
    allow.request.context = json!({"blocked": false});
    let mut deny = allow.clone();
    deny.name = "blocked".into();
    deny.request.context = json!({"blocked": true});
    deny.expected = "deny".into();
    deny.expected_reasons = vec!["blocked".into()];
    let mut manifest = validated(allow.clone());
    let mut schema_value = manifest.schema.deref().clone();
    schema_value[""]["actions"]["view"]["appliesTo"]["context"]["attributes"]["blocked"] =
        json!({"type": "Boolean"});
    manifest.schema = serde_json::from_value(schema_value).unwrap();
    manifest.cases.push(deny);
    let mut entity_metrics = crate::ReplayMetrics::default();
    let rows = crate::replay_validated_manifest_measured(&manifest, &mut entity_metrics)
        .expect("fresh context with shared entities");
    assert_eq!(
        (
            rows[0].replay.decision.as_str(),
            rows[1].replay.decision.as_str()
        ),
        ("allow", "deny")
    );
    assert_eq!(
        (
            entity_metrics.entity_parse_calls,
            entity_metrics.entity_reuses,
            entity_metrics.authorization_calls
        ),
        (1, 1, 4)
    );

    let sources = render_validated_policy_sources(&manifest, "allow-all")
        .expect("strictly validated sources");
    assert_eq!(
        sources.keys().map(String::as_str).collect::<Vec<_>>(),
        ["base", "blocked"]
    );
    let receipts = replay_validated_manifest(&manifest).expect("official Cedar decisions");
    assert_eq!(
        receipts
            .iter()
            .map(|row| row.replay.decision.as_str())
            .collect::<Vec<_>>(),
        ["allow", "deny"]
    );

    let mut invalid_schema = validated(allow.clone());
    invalid_schema.schema = manifest.schema.clone();
    let mut schema_value = invalid_schema.schema.deref().clone();
    schema_value[""]["actions"]["view"]["appliesTo"]["context"]["attributes"] = json!({});
    invalid_schema.schema = serde_json::from_value(schema_value).unwrap();
    assert!(
        render_validated_policy_sources(&invalid_schema, "allow-all")
            .unwrap_err()
            .contains("strict policy validation")
    );
    let mut invalid_entities = validated(allow.clone());
    invalid_entities.schema = manifest.schema.clone();
    invalid_entities.cases[0].entities = serde_json::from_value(json!({})).expect("entity source");
    assert!(
        render_validated_policy_sources(&invalid_entities, "allow-all")
            .unwrap_err()
            .contains("schema entities")
    );
    let mut changed_ids = validated(allow.clone());
    changed_ids.schema = manifest.schema.clone();
    changed_ids.cases[0].policy_ids = vec!["base".into()];
    assert!(
        render_validated_policy_sources(&changed_ids, "allow-all")
            .unwrap_err()
            .contains("policy IDs")
    );
    let mut empty = validated(allow);
    empty.schema = manifest.schema;
    empty.cases[0].policies = serde_json::from_value(json!({
        "staticPolicies": {}, "templates": {}, "templateLinks": []
    }))
    .unwrap();
    assert!(
        render_validated_policy_sources(&empty, "allow-all")
            .unwrap_err()
            .contains("empty")
    );
}

fn validated(case: Case) -> ValidatedManifest {
    ValidatedManifest {
        schema: serde_json::from_value(json!({"": {
            "entityTypes": {
                "User": {"shape": {"type": "Record", "attributes": {}}},
                "Document": {"shape": {"type": "Record", "attributes": {}}}
            },
            "actions": {"view": {"appliesTo": {
                "principalTypes": ["User"],
                "resourceTypes": ["Document"],
                "context": {"type": "Record", "attributes": {}}
            }}}
        }}))
        .unwrap(),
        cases: vec![case],
    }
}

#[test]
fn schema_bound_replay_checks_request_and_binds_schema() {
    let baseline = validated(receipt());
    let receipts = replay_validated_manifest(&baseline).expect("official schema validation");
    assert_eq!(receipts.len(), 1);
    assert_eq!(receipts[0].schema_sha256.len(), 64);
    verify_validated_replay_receipts(&baseline, &receipts).expect("same schema and replay");

    let mut changed = validated(receipt());
    let mut schema_value = changed.schema.deref().clone();
    schema_value[""]["entityTypes"]["Extra"] =
        json!({"shape": {"type": "Record", "attributes": {}}});
    changed.schema = serde_json::from_value(schema_value).unwrap();
    let changed_receipts = replay_validated_manifest(&changed).expect("valid changed schema");
    assert_eq!(
        changed_receipts[0].replay.decision,
        receipts[0].replay.decision
    );
    assert_ne!(changed_receipts[0].schema_sha256, receipts[0].schema_sha256);
    assert!(verify_validated_replay_receipts(&changed, &receipts).is_err());
}

#[test]
fn schema_bound_replay_rejects_wrong_context_and_request_types() {
    let mut context = validated(receipt());
    context.cases[0].request.context = json!({"unlisted": true});
    assert!(
        replay_validated_manifest(&context)
            .unwrap_err()
            .contains("schema context")
    );

    let mut principal = validated(receipt());
    principal.cases[0].request.principal = "Document::\"one\"".into();
    assert!(
        replay_validated_manifest(&principal)
            .unwrap_err()
            .contains("schema request")
    );
}

#[test]
fn schema_bound_replay_rejects_invalid_policy() {
    let mut case = receipt();
    let mut policies = case.policies.deref().clone();
    policies["staticPolicies"]["invalid"] = json!({
        "effect": "permit",
        "principal": {"op": "All"},
        "action": {"op": "All"},
        "resource": {"op": "All"},
        "conditions": [{"kind": "when", "body": {
            ".": {"left": {"Var": "principal"}, "attr": "missing"}
        }}]
    });
    case.policies = serde_json::from_value(policies).unwrap();
    assert!(
        replay_validated_manifest(&validated(case))
            .unwrap_err()
            .contains("strict policy validation")
    );
}

#[test]
fn schema_bound_replay_uses_schema_action_hierarchy_for_authorization() {
    let mut manifest = validated(receipt());
    let mut schema_value = manifest.schema.deref().clone();
    schema_value[""]["actions"]["read"] = json!({"appliesTo": {
        "principalTypes": ["User"],
        "resourceTypes": ["Document"],
        "context": {"type": "Record", "attributes": {}}
    }});
    manifest.schema = serde_json::from_value(schema_value).unwrap();
    let mut schema_value = manifest.schema.deref().clone();
    schema_value[""]["actions"]["view"]["memberOf"] = json!([{"type": "Action", "id": "read"}]);
    manifest.schema = serde_json::from_value(schema_value).unwrap();
    let mut policies = manifest.cases[0].policies.deref().clone();
    policies["staticPolicies"]["base"]["action"] =
        json!({"op": "in", "entity": {"type": "Action", "id": "read"}});
    manifest.cases[0].policies = serde_json::from_value(policies).unwrap();
    assert_eq!(
        replay_validated_manifest(&manifest).unwrap()[0]
            .replay
            .decision,
        "allow"
    );
    assert!(
        check_manifest(&Manifest {
            cases: manifest.cases.clone()
        })
        .is_err()
    );
}

fn optional_attribute_revision() -> SchemaEvolutionBundle {
    let before = validated(receipt());
    let mut after = validated(receipt());
    let mut schema_value = after.schema.deref().clone();
    schema_value[""]["entityTypes"]["Document"]["shape"]["attributes"]["classification"] =
        json!({"type": "String", "required": false});
    after.schema = serde_json::from_value(schema_value).unwrap();
    SchemaEvolutionBundle { before, after }
}

#[test]
fn schema_only_revision_preserves_observed_inputs_and_decision() {
    let bundle = optional_attribute_revision();
    let result = replay_schema_only_revision(&bundle).unwrap();
    assert_ne!(result.before_schema_sha256, result.after_schema_sha256);
    assert_eq!(result.replay.len(), 1);
    assert_eq!(result.replay[0].decision, "allow");
    verify_schema_only_revision(&bundle, &result).unwrap();
    let mut changed = result.clone();
    changed.replay[0].decision = "deny".into();
    assert!(verify_schema_only_revision(&bundle, &changed).is_err());
}

#[test]
fn schema_only_revision_rejects_unchanged_schema_and_input_drift() {
    let same = SchemaEvolutionBundle {
        before: validated(receipt()),
        after: validated(receipt()),
    };
    assert!(
        replay_schema_only_revision(&same)
            .unwrap_err()
            .contains("changed schema")
    );

    let mut drift = optional_attribute_revision();
    drift.after.cases[0].request.principal = "User::\"bob\"".into();
    assert!(
        replay_schema_only_revision(&drift)
            .unwrap_err()
            .contains("artifacts")
    );
}

#[test]
fn accepts_materialized_receipt_and_preserves_id() {
    let case = receipt();
    let policies = load_policy_set(&case.policies).expect("materialized policy set");
    assert_eq!(policies.policies().next().unwrap().id().to_string(), "base");
    check_manifest(&Manifest { cases: vec![case] }).expect("same Cedar decision");
}

#[test]
fn replay_receipt_binds_request_even_when_decision_is_unchanged() {
    let baseline = Manifest {
        cases: vec![receipt()],
    };
    let receipts = replay_manifest(&baseline).expect("official Cedar replay");
    assert_eq!(receipts.len(), 1);
    assert_eq!(receipts[0].format_version, 1);
    assert_eq!(receipts[0].cedar_policy_version, "4.12.0");
    assert_eq!(receipts[0].cedar_language_version, "4.5.0");
    assert_eq!(receipts[0].policies_sha256.len(), 64);
    assert_eq!(receipts[0].decision, "allow");
    assert!(receipts[0].error_free_allow);
    verify_replay_receipts(&baseline, &receipts).expect("same inputs and runtime");

    let mut changed = receipt();
    changed.request.principal = "User::\"bob\"".into();
    let changed_manifest = Manifest {
        cases: vec![changed],
    };
    let changed_receipts = replay_manifest(&changed_manifest).expect("still allowed");
    assert_eq!(changed_receipts[0].decision, receipts[0].decision);
    assert_ne!(
        changed_receipts[0].request_sha256,
        receipts[0].request_sha256
    );
    assert!(verify_replay_receipts(&changed_manifest, &receipts).is_err());
}

#[test]
fn replay_hash_ignores_json_object_key_order() {
    let left: serde_json::Value =
        serde_json::from_str(r#"{"z":{"two":2,"one":1},"a":[{"y":true,"x":false}]}"#)
            .expect("JSON");
    let right: serde_json::Value =
        serde_json::from_str(r#"{"a":[{"x":false,"y":true}],"z":{"one":1,"two":2}}"#)
            .expect("JSON");
    assert_eq!(json_sha256(&left).unwrap(), json_sha256(&right).unwrap());
}

#[test]
fn replay_receipt_rejects_diagnostic_and_version_drift() {
    let manifest = Manifest {
        cases: vec![receipt()],
    };
    let mut receipts = replay_manifest(&manifest).expect("official Cedar replay");
    receipts[0].reasons.clear();
    assert!(verify_replay_receipts(&manifest, &receipts).is_err());
    receipts = replay_manifest(&manifest).expect("official Cedar replay");
    receipts[0].cedar_policy_version = "0.0.0".into();
    assert!(verify_replay_receipts(&manifest, &receipts).is_err());
}

#[test]
fn replay_receipt_exposes_allow_with_an_erroring_forbid() {
    let mut case = receipt();
    let mut policies = case.policies.deref().clone();
    policies["staticPolicies"]["error-guard"] = json!({
        "effect": "forbid",
        "principal": { "op": "All" },
        "action": { "op": "All" },
        "resource": { "op": "All" },
        "conditions": [{
            "kind": "when",
            "body": { ".": { "left": { "Var": "principal" }, "attr": "missing" } }
        }]
    });
    case.policies = serde_json::from_value(policies).expect("two policies");
    case.policy_ids.push("error-guard".into());
    case.expected_error_policies = vec!["error-guard".into()];
    let replayed = replay_manifest(&Manifest { cases: vec![case] }).expect("official Cedar replay");
    assert_eq!(replayed[0].decision, "allow");
    assert_eq!(replayed[0].error_policy_ids, ["error-guard"]);
    assert!(!replayed[0].error_free_allow);
}

#[test]
fn rejects_decision_drift_and_duplicate_case_names() {
    let mut case = receipt();
    case.expected = "deny".into();
    assert!(
        check_manifest(&Manifest { cases: vec![case] })
            .unwrap_err()
            .contains("expected deny")
    );

    let first = receipt();
    let second = receipt();
    assert!(
        check_manifest(&Manifest {
            cases: vec![first, second]
        })
        .unwrap_err()
        .contains("duplicate case name")
    );
}

#[test]
fn rejects_policy_id_drift_from_lean_receipt() {
    let mut case = receipt();
    case.policy_ids = vec!["missing".into()];
    assert!(
        check_manifest(&Manifest { cases: vec![case] })
            .unwrap_err()
            .contains("loaded policy IDs differ")
    );
}

#[test]
fn rejects_unsafe_revision_names_before_artifact_generation() {
    let mut case = receipt();
    case.revision = "../escape".into();
    assert!(
        check_manifest(&Manifest { cases: vec![case] })
            .unwrap_err()
            .contains("invalid revision name")
    );
}

#[test]
fn accepts_dotted_versions_but_not_empty_segments_or_paths() {
    assert!(super::valid_revision_name("attested-governed-0.1"));
    for invalid in ["", ".0.1", "0.1.", "0..1", "../escape", "0/1"] {
        assert!(!super::valid_revision_name(invalid), "{invalid}");
    }
}

#[test]
fn rejects_reason_drift_with_unchanged_decision() {
    let mut case = receipt();
    case.expected_reasons.clear();
    assert!(
        check_manifest(&Manifest { cases: vec![case] })
            .unwrap_err()
            .contains("reasons")
    );
}

#[test]
fn rejects_error_policy_drift_with_unchanged_count() {
    let mut case = receipt();
    case.expected_error_policies = vec!["other".into()];
    assert!(
        check_manifest(&Manifest { cases: vec![case] })
            .unwrap_err()
            .contains("errors")
    );
}

#[test]
fn rejects_template_payload_at_materialized_boundary() {
    let mut case = receipt();
    let mut value = case.policies.deref().clone();
    value["templateLinks"] = json!([{}]);
    case.policies = serde_json::from_value(value).expect("JSON artifact");
    assert!(
        load_policy_set(&case.policies)
            .unwrap_err()
            .contains("only materialized policies")
    );
}

#[test]
fn rejects_conflicting_revision_artifacts() {
    let first = receipt();
    let mut second = receipt();
    second.name = "other".into();
    let mut value = second.policies.deref().clone();
    value["staticPolicies"]["base"]["effect"] = json!("forbid");
    second.policies = serde_json::from_value(value).expect("JSON artifact");
    assert!(
        render_artifacts(&Manifest {
            cases: vec![first, second]
        })
        .unwrap_err()
        .contains("conflicting revision output")
    );
}

#[test]
fn cached_revision_requires_identical_policy_artifacts() {
    let first = receipt();
    let mut second = receipt();
    second.name = "second request".into();
    check_manifest(&Manifest {
        cases: vec![first, second],
    })
    .expect("same revision is reusable");

    let first = receipt();
    let mut second = receipt();
    second.name = "second request".into();
    second.expected = "deny".into();
    assert!(
        check_manifest(&Manifest {
            cases: vec![first, second]
        })
        .unwrap_err()
        .contains("expected deny")
    );

    let first = receipt();
    let mut changed = receipt();
    changed.name = "changed body".into();
    let mut value = changed.policies.deref().clone();
    value["staticPolicies"]["base"]["conditions"] = json!([{
        "kind": "when",
        "body": { "type": "Boolean", "value": true }
    }]);
    changed.policies = serde_json::from_value(value).expect("JSON artifact");
    assert!(
        check_manifest(&Manifest {
            cases: vec![first, changed]
        })
        .unwrap_err()
        .contains("conflicting revision output")
    );
}

#[test]
fn direct_cedar_check_detects_policy_drift() {
    let directory =
        std::env::temp_dir().join(format!("cedar-poo-direct-check-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("temporary directory");
    let path = directory.join("published.cedar");
    let manifest = Manifest {
        cases: vec![receipt()],
    };
    std::fs::write(&path, "permit(principal, action, resource);").expect("direct permit");
    check_direct_sources(&manifest, &directory).expect("matching decision");
    let mut wrong_ids = receipt();
    wrong_ids.policy_ids = vec!["other".into()];
    assert!(
        check_direct_sources(
            &Manifest {
                cases: vec![wrong_ids]
            },
            &directory
        )
        .unwrap_err()
        .contains("loaded policy IDs differ")
    );
    let mut wrong_reasons = receipt();
    wrong_reasons.expected_reasons.clear();
    assert!(
        check_direct_sources(
            &Manifest {
                cases: vec![wrong_reasons]
            },
            &directory
        )
        .unwrap_err()
        .contains("direct Cedar expected")
    );
    std::fs::write(&path, "permit(principal, action, resource) when { true };")
        .expect("different body with the same decision");
    assert!(
        check_direct_sources(&manifest, &directory)
            .unwrap_err()
            .contains("direct policy bodies differ")
    );
    std::fs::write(&path, "forbid(principal, action, resource);").expect("direct forbid");
    assert!(
        check_direct_sources(&manifest, &directory)
            .unwrap_err()
            .contains("direct policy bodies differ")
    );
    std::fs::remove_dir_all(directory).expect("remove temporary directory");
}

#[test]
fn direct_cedar_check_identifies_erroring_policy_with_new_source_ids() {
    let directory =
        std::env::temp_dir().join(format!("cedar-poo-direct-errors-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("temporary directory");
    std::fs::write(
        directory.join("published.cedar"),
        "permit(principal, action, resource) when { principal.missing };\n\
         forbid(principal, action, resource) when { false };",
    )
    .expect("direct policies");
    let mut case = receipt();
    let mut policies = case.policies.deref().clone();
    policies["staticPolicies"]["base"]["conditions"] = json!([{
        "kind": "when",
        "body": { ".": { "left": { "Var": "principal" }, "attr": "missing" } }
    }]);
    policies["staticPolicies"]["other"] = json!({
        "effect": "forbid",
        "principal": { "op": "All" },
        "action": { "op": "All" },
        "resource": { "op": "All" },
        "conditions": [{ "kind": "when", "body": { "Value": false } }]
    });
    case.policies = serde_json::from_value(policies).expect("two policies");
    case.policy_ids.push("other".into());
    case.expected = "deny".into();
    case.expected_reasons.clear();
    case.expected_error_policies = vec!["base".into()];
    let mut manifest = Manifest { cases: vec![case] };
    check_direct_sources(&manifest, &directory).expect("same erroring policy body");

    manifest.cases[0].expected_error_policies = vec!["other".into()];
    assert!(
        check_direct_sources(&manifest, &directory)
            .unwrap_err()
            .contains("direct Cedar expected")
    );
    std::fs::remove_dir_all(directory).expect("remove temporary directory");
}

fn template_source_fixture() -> (serde_json::Value, crate::CompiledPolicyJson) {
    let source = json!({
        "staticPolicies": {},
        "templates": {
            "grant": {
                "effect": "permit",
                "principal": { "op": "==", "slot": "?principal" },
                "action": { "op": "All" },
                "resource": { "op": "All" },
                "conditions": []
            }
        },
        "templateLinks": [{
            "templateId": "grant",
            "newId": "base",
            "values": { "?principal": { "type": "User", "id": "alice" } }
        }]
    });
    let mut materialized = receipt().policies.deref().clone();
    materialized["staticPolicies"]["base"]["principal"] =
        json!({ "op": "==", "entity": { "type": "User", "id": "alice" } });
    let materialized = serde_json::from_value(materialized).expect("policy set JSON");
    (source, materialized)
}

#[test]
fn template_source_requires_exact_linked_policy_bodies() {
    let (source, materialized) = template_source_fixture();
    let typed_source = serde_json::from_value(source.clone()).expect("template source JSON");
    check_template_source(&typed_source, &materialized).expect("matching linked policy");

    let mut changed = source.clone();
    changed["templates"]["grant"]["effect"] = json!("forbid");
    let typed_changed = serde_json::from_value(changed).expect("changed template source JSON");
    assert!(
        check_template_source(&typed_changed, &materialized)
            .unwrap_err()
            .contains("differ from Lean materialization")
    );
    let mut changed = source;
    changed["templateLinks"][0]["values"] = json!({});
    let typed_changed = serde_json::from_value(changed).expect("incomplete template source JSON");
    assert!(
        check_template_source(&typed_changed, &materialized)
            .unwrap_err()
            .contains("template source parse")
    );
}

#[test]
fn template_source_rejects_unlinked_templates() {
    let (mut source, materialized) = template_source_fixture();
    source["templates"]["unused"] = source["templates"]["grant"].clone();
    source["templates"]["unused"]["effect"] = json!("forbid");
    let source = serde_json::from_value(source).expect("template source JSON");
    let parsed = load_template_source(&source).expect("Cedar accepts an unused template");
    assert_eq!(parsed.templates().count(), 2);
    assert!(
        check_template_source(&source, &materialized)
            .unwrap_err()
            .contains("template has no linked policy: unused")
    );
}

#[test]
fn mixed_template_source_checks_static_bodies_and_id_collisions() {
    let (mut source, materialized) = template_source_fixture();
    let static_body = json!({
        "effect": "forbid",
        "principal": { "op": "All" },
        "action": { "op": "All" },
        "resource": { "op": "All" },
        "conditions": []
    });
    source["staticPolicies"]["static-veto"] = static_body.clone();
    let mut expected = materialized.deref().clone();
    expected["staticPolicies"]["static-veto"] = static_body;
    let expected = serde_json::from_value(expected).expect("mixed materialized JSON");
    let typed_source = serde_json::from_value(source.clone()).expect("mixed source JSON");
    check_template_source(&typed_source, &expected).expect("mixed source matches");

    let mut changed = source.clone();
    changed["staticPolicies"]["static-veto"]["effect"] = json!("permit");
    let changed = serde_json::from_value(changed).expect("changed mixed source JSON");
    assert!(
        check_template_source(&changed, &expected)
            .unwrap_err()
            .contains("differ from Lean materialization")
    );

    source["staticPolicies"]["base"] = source["staticPolicies"]["static-veto"].clone();
    let collision = serde_json::from_value(source).expect("collision source JSON");
    assert!(
        check_template_source(&collision, &expected)
            .unwrap_err()
            .contains("template source parse")
    );
}

#[test]
fn measured_replay_retains_receipts_failures_and_actual_reuse_counts() {
    let first = receipt();
    let mut second = receipt();
    second.name = "second".into();
    let mut manifest = Manifest {
        cases: vec![first, second],
    };
    let reference = replay_manifest(&manifest).expect("reference");
    let mut metrics = crate::ReplayMetrics::default();
    let observed = crate::replay_manifest_measured(&manifest, &mut metrics).expect("observed");
    assert_eq!(reference, observed);
    assert_eq!(metrics.prepared_revisions, 1);
    assert_eq!(metrics.authorization_calls, 4);
    manifest.cases[1].revision = "changed".into();
    let mut metrics = crate::ReplayMetrics::default();
    crate::replay_manifest_measured(&manifest, &mut metrics).expect("changed root");
    assert_eq!(metrics.prepared_revisions, 2);
    assert_eq!(metrics.authorization_calls, 4);
    manifest.cases[1].expected = "deny".into();
    assert_eq!(
        replay_manifest(&manifest).expect_err("original failure"),
        crate::replay_manifest_measured(&manifest, &mut metrics)
            .expect_err("same observed failure")
    );
}

#[test]
fn measured_schema_replay_preserves_strict_errors_and_receipt_bindings() {
    let mut manifest = validated(receipt());
    let mut metrics = crate::ReplayMetrics::default();
    let measured =
        crate::replay_validated_manifest_measured(&manifest, &mut metrics).expect("schema replay");
    assert_eq!(
        measured,
        replay_validated_manifest(&manifest).expect("original")
    );
    assert_eq!(metrics.prepared_revisions, 1);
    assert_eq!(metrics.authorization_calls, 2);
    manifest.cases[0].request.context = json!({"unlisted":true});
    assert_eq!(
        crate::replay_validated_manifest_measured(&manifest, &mut metrics)
            .expect_err("strict measured context"),
        replay_validated_manifest(&manifest).expect_err("strict original context")
    );
}

#[test]
fn replay_distinguishes_explicit_empty_geography_from_missing_and_other_values() {
    let mut policies = load_policy_set(&receipt().policies).expect("baseline policy");
    let forbid = cedar_policy::Policy::parse(
        Some("empty-geography".parse().expect("policy ID")),
        r#"forbid(principal, action, resource) when {
            context.input has geography && context.input.geography == ""
        };"#,
    )
    .expect("independent Cedar text");
    policies.add(forbid).expect("distinct policy ID");
    let artifact = policies.to_json().expect("official Cedar JSON");
    let mut cases = Vec::new();
    for (name, input, decision, reasons) in [
        (
            "empty",
            json!({"geography":""}),
            "deny",
            vec!["empty-geography".to_string()],
        ),
        (
            "other",
            json!({"geography":"EU"}),
            "allow",
            vec!["base".to_string()],
        ),
        ("missing", json!({}), "allow", vec!["base".to_string()]),
    ] {
        let mut case = receipt();
        case.name = name.into();
        case.policies = serde_json::from_value(artifact.clone()).expect("artifact");
        case.policy_ids = vec!["base".into(), "empty-geography".into()];
        case.request.context = json!({"input":input});
        case.expected = decision.into();
        case.expected_reasons = reasons;
        cases.push(case);
    }
    let receipts = replay_manifest(&Manifest { cases }).expect("empty and absent are distinct");
    assert_eq!(receipts.len(), 3);
    assert_eq!(receipts[0].decision, "deny");
    assert!(receipts[1].error_free_allow && receipts[2].error_free_allow);
}

#[path = "preparation.rs"]
mod preparation;

// Retain the exact pre-optimization normalizer as an independent test oracle.
fn assert_legacy_revision_bodies(case: &Case) {
    let policies = load_policy_set(&case.policies).expect("compiled JSON policy set");
    let (text, bodies) = crate::policy_codec::rendered_policy_bodies(&policies).expect("render");
    let legacy: std::collections::BTreeMap<_, _> = policies
        .policies()
        .map(|p| {
            (
                p.id().to_string(),
                crate::policy_codec::canonical_policy_body(p).expect("legacy normalization"),
            )
        })
        .collect();
    assert_eq!(bodies, legacy, "compiled AST normalization: {}", case.name);
    let sections = bodies
        .iter()
        .map(|(id, body)| format!("// POO policy ID: {id}\n{body}"))
        .collect::<Vec<_>>();
    assert_eq!(
        text,
        format!(
            "// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.\n{}\n",
            sections.join("\n\n")
        )
    );
}

#[test]
fn json_ast_render_preserves_legacy_normalization_and_source_bytes() {
    // Formatting, annotations, IDs, scopes, literals and condition structure.
    for (index, text) in [
        "permit(principal,action,resource);",
        " // spacing\n permit ( principal, action, resource ) when { true };",
        "@z(\"last\") @a(\"first\") forbid(principal,action,resource) unless { false };",
        "permit(principal == User::\"alice\",action in [Action::\"a\",Action::\"b\"],resource) when { context has x && context.x == 1 };",
        "permit(principal is User,action,resource is Document) when { true } when { false } unless { false };",
        "permit(principal,action,resource) when { [1,2].contains(1) && { x: \"line\\nquote\\\"\", y: -9223372036854775808 }.y < 0 };",
        "permit(principal,action,resource) when { context.ip.isInRange(ip(\"10.0.0.0/8\")) };",
        "permit(principal,action,resource) when { context.name like \"a*\" };",
    ].into_iter().enumerate() {
        let policy = cedar_policy::Policy::parse(None, text).expect("metamorphic source");
        let mut case = receipt();
        let id = format!("revision-{index}");
        let mut source = json!({"staticPolicies":{},"templates":{},"templateLinks":[]});
        source["staticPolicies"][&id] = policy.to_json().expect("source JSON");
        case.policies = serde_json::from_value(source).expect("compiled wire");
        assert_legacy_revision_bodies(&case);
    }
    // Duplicate bodies retain distinct IDs, sorted source order and multiplicity.
    let mut case = receipt();
    let mut source = case.policies.deref().clone();
    source["staticPolicies"]["second"] = source["staticPolicies"]["base"].clone();
    case.policies = serde_json::from_value(source).unwrap();
    assert_legacy_revision_bodies(&case);
    let empty = cedar_policy::PolicySet::new();
    assert_eq!(
        crate::policy_codec::rendered_policy_bodies(&empty)
            .unwrap()
            .0,
        "// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.\n\n"
    );
}
