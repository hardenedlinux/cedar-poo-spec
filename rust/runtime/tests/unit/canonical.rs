use super::{json_sha256, value_sha256};
use serde::Serialize;
use serde_json::Value;
use serde_json::json;
use sha2::{Digest, Sha256};

#[test]
fn borrowed_hash_preserves_legacy_canonical_bytes_and_escaping() {
    let values = [
        json!({"z":"\\\"\n\t😀","a":[true,false,null,-0.0,1.25]}),
        json!({"integer":u64::MAX,"negative":i64::MIN}),
        json!([]),
        json!({}),
        json!("\u{0000}"),
        json!({"β":{"two":2,"one":1}}),
    ];
    for value in values {
        assert_eq!(
            value_sha256(&value).expect("borrowed"),
            legacy_hash(&value).expect("legacy")
        );
        assert_eq!(
            json_sha256(&value).expect("generic"),
            legacy_hash(&value).expect("legacy")
        );
    }
}

fn legacy_hash(value: &impl Serialize) -> Result<String, String> {
    let value = serde_json::to_value(value).map_err(|error| error.to_string())?;
    let mut bytes = Vec::new();
    write_canonical_json(&value, &mut bytes)?;
    let digest = Sha256::digest(bytes);
    Ok(digest.iter().map(|byte| format!("{byte:02x}")).collect())
}

fn write_canonical_json(value: &Value, output: &mut Vec<u8>) -> Result<(), String> {
    match value {
        Value::Null => output.extend_from_slice(b"null"),
        Value::Bool(value) => output.extend_from_slice(if *value { b"true" } else { b"false" }),
        Value::Number(value) => output.extend_from_slice(value.to_string().as_bytes()),
        Value::String(value) => {
            output.extend_from_slice(&serde_json::to_vec(value).map_err(|error| error.to_string())?)
        }
        Value::Array(values) => {
            output.push(b'[');
            for (index, value) in values.iter().enumerate() {
                if index > 0 {
                    output.push(b',');
                }
                write_canonical_json(value, output)?;
            }
            output.push(b']');
        }
        Value::Object(values) => {
            output.push(b'{');
            let mut entries = values.iter().collect::<Vec<_>>();
            entries.sort_unstable_by(|left, right| left.0.cmp(right.0));
            for (index, (key, value)) in entries.into_iter().enumerate() {
                if index > 0 {
                    output.push(b',');
                }
                output.extend_from_slice(
                    &serde_json::to_vec(key).map_err(|error| error.to_string())?,
                );
                output.push(b':');
                write_canonical_json(value, output)?;
            }
            output.push(b'}');
        }
    }
    Ok(())
}

#[test]
fn streaming_hash_preserves_block_boundaries_and_large_escaped_payloads() {
    for length in [0, 1, 1023, 1024, 1025, 2048, 4097] {
        let value =
            json!({"z": ["\\\"\nλ".repeat(length),i64::MIN,u64::MAX],"a":{"zero":-0.0,"one":1.0}});
        assert_eq!(value_sha256(&value), legacy_hash(&value), "length {length}");
    }
}
