use crate::policy_codec::canonical_policy_body;
use cedar_policy::{Policy, PolicySet};
use serde_json::json;
use std::str::FromStr;

// Independent original SDK JSON normalization remains the differential oracle.
fn original(policy: &Policy) -> String {
    Policy::from_json(None, policy.to_json().unwrap())
        .unwrap()
        .to_cedar()
        .unwrap()
}

#[test]
fn typed_normalization_preserves_full_original_bodies_from_text_and_json() {
    for source in [
        "permit(principal, action, resource);",
        "forbid(principal, action, resource) unless { false };",
        "@z(\"μ\\nquoted\\\"\") @a(\"tag\") permit(principal, action, resource);",
        "// leading\n permit ( principal, action, resource ) when { true };",
        "permit(principal == Tenant::User::\"a\", action in [Action::\"b\", Action::\"a\"], resource);",
        "permit(principal, action, resource) when { context.a == -9223372036854775808 };",
        "permit(principal, action, resource) when { context.a == [1, 1, 2] };",
        "permit(principal, action, resource) when { context.a == {x: 1, y: true} };",
        "permit(principal, action, resource) when { resource has tag && resource.tag like \"a*\\*\" };",
        "permit(principal, action, resource) when { ip(\"10.0.0.1\").isInRange(ip(\"10.0.0.0/8\")) };",
        "permit(principal, action, resource) when { decimal(\"1.25\") < decimal(\"2.0\") };",
    ] {
        let text = Policy::from_str(source).expect(source);
        let json = Policy::from_json(None, text.to_json().unwrap()).unwrap();
        for policy in [&text, &json] {
            assert_eq!(
                canonical_policy_body(policy).unwrap(),
                original(policy),
                "{source}"
            );
        }
    }
    let allow = Policy::from_str("permit(principal, action, resource);").unwrap();
    let deny = Policy::from_str("forbid(principal, action, resource);").unwrap();
    assert_ne!(
        canonical_policy_body(&allow).unwrap(),
        canonical_policy_body(&deny).unwrap()
    );
}

#[test]
fn typed_normalization_materializes_actual_link_values_and_preserves_annotations() {
    for id in ["alice", "bob"] {
        let source = json!({
            "staticPolicies": {},
            "templates": {"grant": {
                "effect":"permit", "principal":{"op":"==","slot":"?principal"},
                "action":{"op":"All"}, "resource":{"op":"All"}, "conditions":[],
                "annotations":{"label":"μ"}
            }},
            "templateLinks":[{"templateId":"grant","newId":"linked",
                "values":{"?principal":{"type":"User","id":id}}}]
        });
        let set = PolicySet::from_json_value(source).unwrap();
        let policy = set.policies().next().unwrap();
        assert_eq!(canonical_policy_body(policy).unwrap(), original(policy));
        assert!(canonical_policy_body(policy).unwrap().contains(id));
    }
}
