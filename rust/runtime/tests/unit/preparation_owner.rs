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
