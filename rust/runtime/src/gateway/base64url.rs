//! Strict unpadded base64url encoding of signed original bytes.
use base64::{Engine, engine::general_purpose::URL_SAFE_NO_PAD};
use serde::{Deserialize, Deserializer, Serializer};
/// Encode original signed bytes with the protocol alphabet and no padding.
pub fn serialize<S: Serializer>(value: &[u8], serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(&URL_SAFE_NO_PAD.encode(value))
}
/// Refuse padded or invalid base64url before signature verification.
pub fn deserialize<'de, D: Deserializer<'de>>(decoder: D) -> Result<Vec<u8>, D::Error> {
    let value = String::deserialize(decoder)?;
    if value.len() > 1_398_102 {
        return Err(serde::de::Error::custom("oversized base64url value"));
    }
    URL_SAFE_NO_PAD
        .decode(value)
        .map_err(serde::de::Error::custom)
}
