use crate::{JsonSourceIdentity, SchemaSourceJson};
use serde_json::json;
use std::ops::Deref;

#[test]
fn shared_schema_preserves_complete_source_and_wire_without_mutable_aliases() {
    let value = json!({"namespace": {"type": "Record", "zero": 0.0, "label": "雪"}});
    let first = serde_json::from_value::<SchemaSourceJson>(value.clone()).unwrap();
    let identity = first.source_identity().unwrap();
    let shared = first.clone();
    assert!(std::ptr::eq(first.deref(), shared.deref()));
    assert!(std::ptr::eq(identity, shared.source_identity().unwrap()));
    let independent: SchemaSourceJson = serde_json::from_value(value.clone()).unwrap();
    assert!(!std::ptr::eq(first.deref(), independent.deref()));
    assert!(first.same_source(&independent));
    assert_eq!(identity, value.encode_source().unwrap());
    assert_eq!(identity, independent.source_identity().unwrap());
    let mut edited = value;
    edited["namespace"]["zero"] = json!(-0.0);
    let changed = serde_json::from_value::<SchemaSourceJson>(edited).unwrap();
    assert_eq!(
        first.deref(),
        changed.deref(),
        "JSON numeric equality loses signed zero"
    );
    assert!(!first.same_source(&changed));
    assert_ne!(identity, changed.source_identity().unwrap());
    assert!(
        first.same_source(&shared),
        "a changed publication cannot mutate the shared source"
    );
}
