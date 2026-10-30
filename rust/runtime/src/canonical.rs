//! Canonical receipt hashing: borrow existing Values and write escaped strings directly.
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

pub(crate) fn json_sha256(value: &impl Serialize) -> Result<String, String> {
    let value = serde_json::to_value(value).map_err(|error| error.to_string())?;
    value_sha256(&value)
}

pub(crate) fn value_sha256(value: &Value) -> Result<String, String> {
    let mut bytes = Vec::new();
    write_canonical_json(value, &mut bytes)?;
    let digest = Sha256::digest(bytes);
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(HEX[usize::from(byte >> 4)] as char);
        encoded.push(HEX[usize::from(byte & 15)] as char);
    }
    Ok(encoded)
}

fn write_canonical_json(value: &Value, output: &mut Vec<u8>) -> Result<(), String> {
    match value {
        Value::Null => output.extend_from_slice(b"null"),
        Value::Bool(value) => output.extend_from_slice(if *value { b"true" } else { b"false" }),
        Value::Number(value) => output.extend_from_slice(value.to_string().as_bytes()),
        Value::String(value) => {
            serde_json::to_writer(&mut *output, value).map_err(|error| error.to_string())?
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
                serde_json::to_writer(&mut *output, key).map_err(|error| error.to_string())?;
                output.push(b':');
                write_canonical_json(value, output)?;
            }
            output.push(b'}');
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "../tests/unit/canonical.rs"]
mod tests;
