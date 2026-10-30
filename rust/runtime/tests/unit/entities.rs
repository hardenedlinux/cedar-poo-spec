use super::EntitySlot;
use crate::ReplayMetrics;
use serde_json::json;
#[test]
fn exact_snapshot_changes_and_failed_parse_do_not_poison_a_later_hit() {
    let first = json!([{"uid":{"type":"User","id":"alice"},"attrs":{"enabled":true},"parents":[]}]);
    let changed =
        json!([{"uid":{"type":"User","id":"alice"},"attrs":{"enabled":false},"parents":[]}]);
    let invalid = json!({"not":"an entity array"});
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
    assert!(slot.get(&invalid, Some(&mut stats)).is_err());
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
