use super::SourcePolicies;
use crate::policy_codec::{load_policy_set, policy_bodies_by_id, policy_body_counts};
use crate::preparation::ParsedTextPolicies;
use cedar_policy::PolicySet;
use std::{str::FromStr, sync::Arc};

fn source(text: &str) -> SourcePolicies {
    let value = PolicySet::from_str(text).unwrap().to_json().unwrap();
    let source = serde_json::from_value(value).unwrap();
    let policies = Arc::new(load_policy_set(&source).unwrap());
    SourcePolicies {
        revision: "body-binding".into(),
        source,
        policies,
    }
}

#[test]
fn typed_body_binding_matches_independent_normalizer_across_static_shapes() {
    for text in [
        "",
        "permit(principal, action, resource);",
        "forbid(principal, action, resource) unless { false };",
        "@z(\"μ\\nquoted\\\"\") @a(\"tag\") permit(principal, action, resource);",
        "// leading\n permit ( principal, action, resource ) when { true };",
        "permit(principal == Tenant::User::\"a\", action in [Action::\"b\", Action::\"a\"], resource);",
        "permit(principal, action, resource) when { context.a == -9223372036854775808 };",
        "permit(principal, action, resource) when { context.a == [1, 1, 2] };",
        "permit(principal, action, resource) when { context.a == {y: true, x: 1} };",
        "permit(principal, action, resource) when { resource has tag && resource.tag like \"a*\\*\" };",
        "permit(principal, action, resource) when { ip(\"10.0.0.1\").isInRange(ip(\"10.0.0.0/8\")) };",
        "permit(principal, action, resource) when { decimal(\"1.25\") < decimal(\"2.0\") };",
        "permit(principal, action, resource); permit(principal, action, resource); forbid(principal, action, resource);",
    ] {
        let owner = source(text);
        let generated = owner.render().unwrap();
        let parsed = ParsedTextPolicies::parse(&generated.text).unwrap();
        let original = policy_bodies_by_id(parsed.policies()).unwrap();
        assert_eq!(
            generated.bind_parsed(&parsed).expect(text),
            original,
            "{text}"
        );
    }
}

#[test]
fn binding_preserves_actual_parsed_ids_beyond_ten_policies_and_source_renaming() {
    let text = (0..24)
        .map(|i| {
            format!(
                "@label(\"{i}\") permit(principal, action, resource) when {{ context.n == {i} }};"
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let mut value = PolicySet::from_str(&text).unwrap().to_json().unwrap();
    let policies = value["staticPolicies"].as_object_mut().unwrap();
    let renamed = std::mem::take(policies)
        .into_iter()
        .enumerate()
        .map(|(i, (_, body))| (format!("μ-source-{}", 23 - i), body))
        .collect();
    *policies = renamed;
    let artifact = serde_json::from_value(value).unwrap();
    let owner = SourcePolicies {
        revision: "renamed".into(),
        policies: Arc::new(load_policy_set(&artifact).unwrap()),
        source: artifact,
    };
    let generated = owner.render().unwrap();
    let parsed = ParsedTextPolicies::parse(&generated.text).unwrap();
    let actual = generated.bind_parsed(&parsed).unwrap();
    assert_eq!(actual, policy_bodies_by_id(parsed.policies()).unwrap());
    assert_eq!(actual.len(), 24);
    assert!(actual.keys().all(|id| id.starts_with("policy")));
}

#[test]
fn typed_hint_misses_cannot_hide_changed_annotations_bodies_or_multiplicity() {
    let owner = source("@label(\"a\") permit(principal, action, resource);");
    let generated = owner.render().unwrap();
    for changed in [
        "@label(\"b\") permit(principal, action, resource);",
        "@label(\"a\") forbid(principal, action, resource);",
        "@label(\"a\") permit(principal == User::\"other\", action, resource);",
        "@label(\"a\") permit(principal, action, resource) when { false };",
        "@label(\"a\") permit(principal, action, resource); permit(principal, action, resource);",
    ] {
        let parsed = ParsedTextPolicies::parse(changed).unwrap();
        assert!(generated.bind_parsed(&parsed).is_none(), "{changed}");
        assert_ne!(
            policy_body_counts(&generated.bodies),
            policy_body_counts(&policy_bodies_by_id(parsed.policies()).unwrap())
        );
    }
    let duplicate_owner = source(
        "permit(principal, action, resource); permit(principal, action, resource); forbid(principal, action, resource);",
    );
    let duplicate = duplicate_owner.render().unwrap();
    let parsed = ParsedTextPolicies::parse("permit(principal, action, resource); forbid(principal, action, resource); forbid(principal, action, resource);").unwrap();
    assert!(duplicate.bind_parsed(&parsed).is_none());
    assert_ne!(
        policy_body_counts(&duplicate.bodies),
        policy_body_counts(&policy_bodies_by_id(parsed.policies()).unwrap())
    );
}

#[test]
fn permutation_keeps_original_oracle_and_templates_do_not_bind_empty_sources() {
    let owner = source("permit(principal, action, resource); forbid(principal, action, resource);");
    let generated = owner.render().unwrap();
    let parsed = ParsedTextPolicies::parse(
        "forbid(principal, action, resource); permit(principal, action, resource);",
    )
    .unwrap();
    assert!(generated.bind_parsed(&parsed).is_none());
    assert_eq!(
        policy_body_counts(&generated.bodies),
        policy_body_counts(&policy_bodies_by_id(parsed.policies()).unwrap())
    );
    let empty_owner = source("");
    let empty = empty_owner.render().unwrap();
    let template =
        ParsedTextPolicies::parse("permit(principal == ?principal, action, resource);").unwrap();
    assert!(empty.bind_parsed(&template).is_none());
}
