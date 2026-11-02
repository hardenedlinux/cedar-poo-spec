//! Exact canonical JSON source identity for immutable preparation, not authority.
use serde_json::Value;
use std::io::{self, Write};

// Two serializer passes avoid geometric buffer growth without retaining wire.
// Both use the same immutable Value and default serializer, so sizing preserves
// exact numeric, escaping and object-order behavior.
struct EncodedLength(usize);
impl Write for EncodedLength {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.0 = self.0.checked_add(bytes.len()).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "encoded source length overflow")
        })?;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
fn same_json_source(left: &Value, right: &Value) -> bool {
    if std::ptr::eq(left, right) {
        return true;
    }
    match (left, right) {
        (Value::Number(a), Value::Number(b)) if a.is_f64() && b.is_f64() => {
            a == b && a.as_f64().map(f64::to_bits) == b.as_f64().map(f64::to_bits)
        }
        (Value::Array(a), Value::Array(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(x, y)| same_json_source(x, y))
        }
        (Value::Object(a), Value::Object(b)) => {
            a.len() == b.len()
                && a.iter()
                    .zip(b)
                    .all(|((k, x), (l, y))| k == l && same_json_source(x, y))
        }
        _ => left == right,
    }
}

/// Exact immutable JSON source identity; equality includes numeric signed zero
/// and object representation order. This capability performs no Cedar admission.
pub trait JsonSourceIdentity {
    /// Compare complete source content, preserving canonical receipt bytes.
    fn same_source(&self, other: &Self) -> bool;
    /// Encode the complete source as a collision-free lookup key.
    fn encode_source(&self) -> Result<String, String>;
}
impl JsonSourceIdentity for Value {
    fn same_source(&self, other: &Self) -> bool {
        same_json_source(self, other)
    }
    fn encode_source(&self) -> Result<String, String> {
        let mut size = EncodedLength(0);
        serde_json::to_writer(&mut size, self).map_err(|e| e.to_string())?;
        let mut encoded = Vec::with_capacity(size.0);
        serde_json::to_writer(&mut encoded, self).map_err(|e| e.to_string())?;
        String::from_utf8(encoded).map_err(|e| e.to_string())
    }
}
