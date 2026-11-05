use super::ValidatedProgram;
use crate::{Case, ReplayMetrics, ValidatedManifest, replay_validated_manifest};
use serde_json::json;
use std::sync::Arc;

fn fixture() -> ValidatedManifest {
    serde_json::from_value(json!({
        "schema":{"":{"entityTypes":{
            "User":{"shape":{"type":"Record","attributes":{}}},
            "Document":{"shape":{"type":"Record","attributes":{}}}
        },"actions":{"view":{"appliesTo":{"principalTypes":["User"],"resourceTypes":["Document"],"context":{"type":"Record","attributes":{"ok":{"type":"Boolean"}}}}}}}},
        "cases":[{"name":"fresh-world","revision":"published","policy_ids":["base"],
            "policies":{"staticPolicies":{"base":{"effect":"permit","principal":{"op":"All"},"action":{"op":"All"},"resource":{"op":"All"},"conditions":[{"kind":"when","body":{".":{"left":{"Var":"context"},"attr":"ok"}}}]}},"templates":{},"templateLinks":[]},
            "entities":[],"request":{"principal":"User::\"alice\"","action":"Action::\"view\"","resource":"Document::\"one\"","context":{"ok":true}},
            "expected":"allow","expected_reasons":["base"],"expected_error_policies":[]}]
    })).unwrap()
}
fn original(
    schema: &cedar_poo_core::SchemaSourceJson,
    case: &Case,
) -> Result<crate::SchemaBoundReceipt, String> {
    replay_validated_manifest(&ValidatedManifest {
        schema: schema.clone(),
        cases: vec![case.clone()],
    })
    .map(|mut receipts| receipts.remove(0))
}
#[test]
fn reuse_keeps_fresh_worlds_both_authorizers_expectations_and_exact_receipts() {
    let fixture = fixture();
    let base = &fixture.cases[0];
    let (program, first) = ValidatedProgram::prepare(&fixture.schema, base).unwrap();
    assert_eq!(first, original(&fixture.schema, base).unwrap());
    let mut changed = base.clone();
    changed.request.context = json!({"ok":false});
    changed.expected = "deny".into();
    changed.expected_reasons.clear();
    for case in [base, &changed, base] {
        let mut metrics = ReplayMetrics::default();
        let actual = program.replay_measured(case, &mut metrics).unwrap();
        assert_eq!(actual, original(&fixture.schema, case).unwrap());
        assert_eq!(metrics.schema_parse_calls, 0);
        assert_eq!(metrics.source_policy_loads, 0);
        assert_eq!(metrics.policy_validation_calls, 0);
        assert_eq!(metrics.source_policy_reuses, 1);
        assert_eq!(metrics.revision_syntax_reuses, 1);
        assert_eq!(metrics.entity_parse_calls, 1);
        assert_eq!(metrics.authorization_calls, 2);
    }
    let mut bad = base.clone();
    bad.request.principal = "Document::\"one\"".into();
    assert_eq!(
        program.replay(&bad).unwrap_err(),
        original(&fixture.schema, &bad).unwrap_err()
    );
    bad = base.clone();
    bad.policy_ids.clear();
    assert_eq!(
        program.replay(&bad).unwrap_err(),
        original(&fixture.schema, &bad).unwrap_err()
    );
    bad = base.clone();
    bad.expected = "deny".into();
    assert_eq!(
        program.replay(&bad).unwrap_err(),
        original(&fixture.schema, &bad).unwrap_err()
    );
    assert_eq!(program.replay(base).unwrap(), first);
}
#[test]
fn changed_policy_or_schema_requires_fresh_bound_validation_and_old_sources_retire() {
    let fixture = fixture();
    let base = &fixture.cases[0];
    let (program, first) = ValidatedProgram::prepare(&fixture.schema, base).unwrap();
    let old_policy = Arc::downgrade(&program.revision.policies);
    let schema = Arc::downgrade(&program.schema);
    let mut changed = base.clone();
    let mut source = (*changed.policies).clone();
    source["staticPolicies"]["base"]["effect"] = json!("forbid");
    changed.policies = serde_json::from_value(source).unwrap();
    changed.expected = "deny".into();
    assert!(program.replay(&changed).is_err());
    let (next, receipt) = program.revise(&changed).unwrap();
    assert_eq!(receipt, original(&fixture.schema, &changed).unwrap());
    assert_eq!(program.replay(base).unwrap(), first);
    assert!(Arc::ptr_eq(&program.schema, &next.schema));
    assert!(!Arc::ptr_eq(
        &program.revision.policies,
        &next.revision.policies
    ));
    let mut other_schema = (*fixture.schema).clone();
    other_schema[""]["entityTypes"]["Extra"] = json!({"shape":{"type":"Record","attributes":{}}});
    let other_schema = serde_json::from_value(other_schema).unwrap();
    let (_, other) = ValidatedProgram::prepare(&other_schema, base).unwrap();
    assert_ne!(other.schema_sha256, first.schema_sha256);
    let mut invalid = base.clone();
    let mut source = (*invalid.policies).clone();
    source["staticPolicies"]["base"]["conditions"][0]["body"] =
        json!({".":{"left":{"Var":"principal"},"attr":"missing"}});
    invalid.policies = serde_json::from_value(source).unwrap();
    assert_eq!(
        program.revise(&invalid).err().unwrap(),
        original(&fixture.schema, &invalid).unwrap_err()
    );
    assert_eq!(program.replay(base).unwrap(), first);
    let mut invalid_schema = (*fixture.schema).clone();
    invalid_schema[""]["actions"]["view"]["appliesTo"]["context"]["attributes"]["ok"]["type"] =
        json!("Long");
    let invalid_schema = serde_json::from_value(invalid_schema).unwrap();
    assert_eq!(
        ValidatedProgram::prepare(&invalid_schema, base)
            .err()
            .unwrap(),
        original(&invalid_schema, base).unwrap_err()
    );
    drop(program);
    assert!(old_policy.upgrade().is_none());
    assert!(schema.upgrade().is_some());
    drop(next);
    assert!(schema.upgrade().is_none());
}
