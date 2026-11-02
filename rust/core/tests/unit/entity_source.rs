use crate::EntitySourceJson;
use std::ops::Deref;

#[test]
fn shared_value_keeps_source_identity_without_retained_wire() {
    let value = serde_json::json!([{"uid":{"type":"User","id":"雪"},"attrs":{},"parents":[]}]);
    let a: EntitySourceJson = serde_json::from_value(value.clone()).unwrap();
    let b: EntitySourceJson = serde_json::from_value(value.clone()).unwrap();
    let shared = a.clone();
    let wire = crate::JsonSourceIdentity::encode_source(a.deref()).unwrap();
    assert_eq!(a, b, "a memoized encoding is not entity value state");
    assert!(std::ptr::eq(a.deref(), shared.deref()));
    assert_eq!(serde_json::to_value(&a).unwrap(), value);
    assert_eq!(wire, serde_json::to_string(&value).unwrap());
    assert_eq!(
        wire,
        crate::JsonSourceIdentity::encode_source(b.deref()).unwrap()
    );
}

#[test]
fn numeric_source_equality_matches_the_actual_encoding() {
    use crate::JsonSourceIdentity;
    let values = [
        "0",
        "0.0",
        "-0.0",
        "1.0",
        "1e0",
        "1",
        "18446744073709551615",
    ]
    .map(|s| serde_json::from_str::<serde_json::Value>(s).unwrap());
    for a in &values {
        for b in &values {
            assert_eq!(
                a.same_source(b),
                a.encode_source().unwrap() == b.encode_source().unwrap()
            );
        }
    }
}

#[test]
fn exact_source_encoding_preserves_unicode_escapes_and_large_nested_values() {
    use crate::JsonSourceIdentity;
    let values = [
        serde_json::json!(null),
        serde_json::json!("\u{0}\n\r\t\"\\雪🙂"),
        serde_json::json!({"quote\"": [true, false, -0.0, u64::MAX], "empty": {}}),
        serde_json::json!(
            (0..1024)
                .map(|i| serde_json::json!({"id": i, "value": "雪🙂\n\\"}))
                .collect::<Vec<_>>()
        ),
    ];
    for value in values {
        let wire = value.encode_source().unwrap();
        assert_eq!(wire, serde_json::to_string(&value).unwrap());
        assert!(
            serde_json::from_str::<serde_json::Value>(&wire)
                .unwrap()
                .same_source(&value)
        );
    }
}
