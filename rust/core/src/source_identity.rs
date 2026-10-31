//! Exact canonical JSON source identity for immutable preparation, not authority.
use serde_json::Value;
fn same_json_source(left: &Value, right: &Value) -> bool {
    if std::ptr::eq(left, right) {
        return true;
    }
    match (left, right) {
        (Value::Number(a), Value::Number(b)) if a.is_f64() && b.is_f64() => {
            a.as_f64().map(f64::to_bits) == b.as_f64().map(f64::to_bits)
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
        serde_json::to_string(self).map_err(|e| e.to_string())
    }
}
