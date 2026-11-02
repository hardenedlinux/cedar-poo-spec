use super::SyntaxPreparation;
use crate::{CatalogPreparation, CompiledPolicyJson, Manifest, ReplayMetrics};
use serde_json::json;
use std::ops::Deref;
fn source() -> CompiledPolicyJson {
    serde_json::from_str(r#"{"staticPolicies":{"base":{"effect":"permit","principal":{"op":"All"},"action":{"op":"All"},"resource":{"op":"All"},"conditions":[]}},"templates":{},"templateLinks":[]}"#).unwrap()
}
#[test]
fn finite_syntax_plan_retires_only_on_last_distinct_manifest_use() {
    let source = source();
    let key = source.source_identity().unwrap();
    let mut plan =
        SyntaxPreparation::plan([vec![source.clone(), source.clone()], vec![source.clone()]])
            .unwrap();
    assert_eq!(plan.slots[key].remaining, 2);
    let compiled = std::sync::Arc::new(crate::load_policy_set(&source).unwrap());
    plan.remember_compiled(key, compiled.clone());
    assert_eq!(plan.retained(), 1);
    let cases = manifest().cases;
    assert_eq!(plan.finish(&cases).unwrap(), 0);
    assert!(std::sync::Arc::ptr_eq(
        &compiled,
        &plan.compiled(key).unwrap()
    ));
    assert_eq!(plan.finish(&cases).unwrap(), 1);
    assert!(plan.slots.is_empty());
    plan.remember_compiled(key, compiled);
    assert_eq!(
        plan.retained(),
        0,
        "retired/unplanned sources cannot reopen slots"
    );
}
fn manifest() -> Manifest {
    serde_json::from_value(json!({"cases":[{
        "name":"same", "revision":"one", "policy_ids":["base"], "policies":(*source()).clone(),
        "entities":[], "request":{"principal":"User::\"a\"","action":"Action::\"read\"","resource":"Doc::\"a\"","context":{}},
        "expected":"allow","expected_reasons":["base"],"expected_error_policies":[]
    }]})).unwrap()
}
#[test]
fn catalog_syntax_reuse_preserves_fresh_requests_and_receipts() {
    let first = manifest();
    let mut second = manifest();
    second.cases[0].name = "second".into();
    let mut owner = CatalogPreparation::from_sources([], [vec![source()], vec![source()]]).unwrap();
    let mut metrics = ReplayMetrics::default();
    for input in [&first, &second] {
        assert_eq!(
            owner.replay(input, Some(&mut metrics)).unwrap(),
            crate::replay_manifest(input).unwrap()
        );
    }
    assert_eq!(metrics.source_policy_loads, 1);
    assert_eq!(metrics.catalog_policy_reuses, 1);
    assert_eq!(metrics.revision_syntax_reuses, 1);
    assert_eq!(metrics.authorization_calls, 4);
    assert_eq!(metrics.uid_parse_calls, 6, "UID owner remains per manifest");
    assert_eq!(metrics.catalog_syntax_retirements, 1);
    assert_eq!(metrics.catalog_syntax_slot_peak, 1);
    assert!(owner.replay(&first, Some(&mut metrics)).is_ok());
    assert_eq!(
        metrics.source_policy_loads, 2,
        "last-use retirement actually forces a fresh parse"
    );
}

#[test]
fn shared_syntax_never_reuses_schema_admission_or_request_context() {
    use crate::{ValidatedManifest, replay_validated_manifest};
    let make = || {
        ValidatedManifest {
        schema: serde_json::from_value(json!({"": {"entityTypes": {
            "User": {"shape":{"type":"Record","attributes":{}}},
            "Doc": {"shape":{"type":"Record","attributes":{}}}},
            "actions":{"read":{"appliesTo":{"principalTypes":["User"],"resourceTypes":["Doc"],"context":{"type":"Record","attributes":{}}}}}}})).unwrap(),
        cases: manifest().cases,
    }
    };
    let mut owner = CatalogPreparation::from_sources(
        [],
        [
            vec![source()],
            vec![source()],
            vec![source()],
            vec![source()],
        ],
    )
    .unwrap();
    let mut metrics = ReplayMetrics::default();
    let baseline = make();
    assert_eq!(
        owner
            .replay_validated(&baseline, Some(&mut metrics))
            .unwrap(),
        replay_validated_manifest(&baseline).unwrap()
    );
    let mut context = make();
    context.cases[0].request.context = json!({"unexpected":true});
    assert_eq!(
        owner
            .replay_validated(&context, Some(&mut metrics))
            .unwrap_err(),
        replay_validated_manifest(&context).unwrap_err()
    );
    let mut schema = make();
    let mut schema_value = schema.schema.deref().clone();
    schema_value[""]["actions"]["read"]["appliesTo"]["context"]["attributes"]["required"] =
        json!({"type":"Boolean","required":true});
    schema.schema = serde_json::from_value(schema_value).unwrap();
    assert_eq!(
        owner
            .replay_validated(&schema, Some(&mut metrics))
            .unwrap_err(),
        replay_validated_manifest(&schema).unwrap_err()
    );
    let mut malformed_schema = make();
    malformed_schema.schema = serde_json::from_value(json!({"invalid":false})).unwrap();
    assert_eq!(
        owner
            .replay_validated(&malformed_schema, Some(&mut metrics))
            .unwrap_err(),
        replay_validated_manifest(&malformed_schema).unwrap_err()
    );
    assert_eq!(metrics.source_policy_loads, 1);
    assert_eq!(
        metrics.policy_validation_calls, 3,
        "strict validation remains fresh even when syntax is identical"
    );
    assert_eq!(
        metrics.authorization_calls, 2,
        "malformed contexts never reach authorizers"
    );
    assert_eq!(metrics.catalog_syntax_retirements, 1);
}

#[test]
fn failed_sdk_source_is_never_retained_and_changed_source_never_hits() {
    use crate::preparation::PreparedReplay;
    let invalid: CompiledPolicyJson =
        serde_json::from_value(json!({"staticPolicies":{"bad":{}}})).unwrap();
    let valid = source();
    let mut plan = SyntaxPreparation::plan([
        vec![invalid.clone(), valid.clone()],
        vec![invalid.clone(), valid.clone()],
    ])
    .unwrap();
    let mut metrics = ReplayMetrics::default();
    let mut invocation = PreparedReplay::sharing(&mut plan);
    assert!(invocation.compiled(&invalid, Some(&mut metrics)).is_err());
    assert!(invocation.compiled(&valid, Some(&mut metrics)).is_ok());
    assert!(invocation.compiled(&invalid, Some(&mut metrics)).is_err());
    drop(invocation);
    assert_eq!(plan.retained(), 1);
    assert!(plan.compiled(invalid.source_identity().unwrap()).is_none());
    assert_eq!(metrics.catalog_policy_reuses, 0);
}
