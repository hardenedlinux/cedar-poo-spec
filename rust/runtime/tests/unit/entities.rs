use super::EntitySlot;
use crate::ReplayMetrics;
use serde_json::json;
#[test]
fn exact_snapshot_changes_and_failed_parse_do_not_poison_a_later_hit() {
    let first = json!([{"uid":{"type":"User","id":"alice"},"attrs":{"enabled":true},"parents":[]}]);
    let changed =
        json!([{"uid":{"type":"User","id":"alice"},"attrs":{"enabled":false},"parents":[]}]);
    let invalid = json!({"not":"an entity array"});
    let first: cedar_poo_core::EntitySourceJson = serde_json::from_value(first).unwrap();
    let changed: cedar_poo_core::EntitySourceJson = serde_json::from_value(changed).unwrap();
    let invalid: cedar_poo_core::EntitySourceJson = serde_json::from_value(invalid).unwrap();
    let mut slot = EntitySlot::new(None);
    let mut stats = ReplayMetrics::default();
    let initial = slot
        .get(&first, Some(&mut stats))
        .expect("first snapshot")
        .clone();
    assert!(
        slot.get(&first, Some(&mut stats))
            .expect("exact hit")
            .deep_eq(&initial)
    );
    assert!(
        !slot
            .get(&changed, Some(&mut stats))
            .expect("same UID changed body")
            .deep_eq(&initial)
    );
    let original = cedar_policy::Entities::from_json_value((*invalid).clone(), None)
        .unwrap_err()
        .to_string();
    assert_eq!(
        slot.get(&invalid, Some(&mut stats))
            .unwrap_err()
            .to_string(),
        original
    );
    assert_eq!(stats.entity_diagnostic_reparses, 1);
    assert!(
        !slot
            .get(&changed, Some(&mut stats))
            .expect("retry retained valid state")
            .deep_eq(&initial)
    );
    assert!(
        slot.get(&first, Some(&mut stats))
            .expect("churn back must rebuild")
            .deep_eq(&initial)
    );
    assert_eq!(
        (
            stats.entity_parse_calls,
            stats.entity_reuses,
            stats.entity_replacements,
            stats.entity_slot_peak
        ),
        (4, 2, 2, 1)
    );
}

#[test]
fn digest_identity_does_not_alias_signed_zero_or_changed_source() {
    let first = serde_json::json!({"x":0.0});
    let second = serde_json::json!({"x":-0.0});
    assert_eq!(
        first, second,
        "Value equality alone loses signed-zero source identity"
    );
    let mut slot = super::EntitySlot::new(None);
    let mut metrics = crate::ReplayMetrics::default();
    let a = slot.receipt_digest(&first, Some(&mut metrics)).unwrap();
    let b = slot.receipt_digest(&second, Some(&mut metrics)).unwrap();
    assert_ne!(a, b);
    assert_eq!(slot.receipt_digest(&second, Some(&mut metrics)).unwrap(), b);
    assert_eq!(
        (metrics.entity_hash_calls, metrics.entity_hash_reuses),
        (2, 1)
    );
}
