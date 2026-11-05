#[test]
fn policy_body_preparation_keys_complete_parsed_text_including_formatting() {
    use super::{ParsedTextPolicies, PreparedReplay};
    use crate::policy_codec::policy_bodies_by_id;
    let mut prepared = PreparedReplay::default();
    let mut metrics = crate::ReplayMetrics::default();
    for text in [
        "permit(principal, action, resource);",
        "permit(principal, action, resource);",
        "permit( principal, action, resource );",
        "forbid(principal, action, resource);",
    ] {
        let parsed = ParsedTextPolicies::parse(text).expect("static parsed source");
        let actual = prepared
            .bodies_by_id(&parsed, Some(&mut metrics))
            .expect("prepared bodies");
        assert_eq!(
            actual,
            policy_bodies_by_id(&parsed.policies).expect("uncached original normalizer")
        );
    }
    assert_eq!(metrics.policy_body_normalizations, 3);
    assert_eq!(metrics.policy_body_reuses, 1);
    assert_eq!(metrics.policy_body_slot_peak, 3);
}

#[test]
fn uid_owner_reuses_exact_successful_syntax_and_retires_with_invocation() {
    use super::PreparedReplay;
    use crate::ReplayMetrics;
    use cedar_policy::EntityUid;
    use std::str::FromStr;
    let mut owner = PreparedReplay::default();
    let mut metrics = ReplayMetrics::default();
    for source in [
        "User::\"alice\"",
        "User::\"alice\"",
        "User::\"bob\"",
        "invalid",
        "invalid",
    ] {
        assert_eq!(
            owner.uid(source, Some(&mut metrics)).ok(),
            EntityUid::from_str(source).ok()
        );
    }
    assert_eq!(
        (
            metrics.uid_parse_calls,
            metrics.uid_reuses,
            metrics.uid_slot_peak
        ),
        (2, 1, 2)
    );
    assert_eq!(owner.uids.len(), 2, "failed parses cannot seed the owner");
    let mut next = PreparedReplay::default();
    next.uid("User::\"alice\"", Some(&mut metrics)).unwrap();
    assert_eq!(
        metrics.uid_parse_calls, 3,
        "new invocation must prepare independently"
    );
}

#[test]
fn one_source_slot_preserves_both_receipt_modes_and_distinct_source_bindings() {
    use super::PreparedReplay;
    use crate::{input::Case, syntax::CheckedRevision};
    use serde_json::json;
    let mut owner = PreparedReplay::default();
    let mut metrics = crate::ReplayMetrics::default();
    for effect in ["permit", "forbid"] {
        let case:Case=serde_json::from_value(json!({
            "name":"slot", "revision":"one", "policy_ids":["base"],
            "policies":{"staticPolicies":{"base":{"effect":effect,"principal":{"op":"All"},"action":{"op":"All"},"resource":{"op":"All"},"conditions":[]}},"templates":{},"templateLinks":[]},
            "entities":[],"request":{"principal":"User::\"a\"","action":"Action::\"read\"","resource":"Doc::\"a\"","context":{}},
            "expected":"allow","expected_reasons":["base"],"expected_error_policies":[]
        })).unwrap();
        for hash in [false, true, false, true] {
            let actual =
                CheckedRevision::new(&case, hash, Some(&mut metrics), Some(&mut owner)).unwrap();
            let independent = CheckedRevision::new(&case, hash, None, None).unwrap();
            assert_eq!(actual.policy_sha256, independent.policy_sha256);
            assert_eq!(actual.compiled_bodies, independent.compiled_bodies);
            assert_eq!(actual.rendered_bodies, independent.rendered_bodies);
            assert!(actual.source.same_source(&case.policies));
        }
    }
    assert_eq!(
        owner.syntax.len(),
        2,
        "one complete source key per different body"
    );
    for slot in owner.syntax.values() {
        assert!(slot.checked.iter().all(Option::is_some));
    }
    assert_eq!(metrics.source_policy_loads, 2);
    assert_eq!(metrics.source_policy_reuses, 6);
    assert_eq!(metrics.revision_syntax_reuses, 4);
}
