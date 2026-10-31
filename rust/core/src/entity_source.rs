//! Immutable complete entity source; ownership is not SDK validity or admission.
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::Value;
use std::{ops::Deref, sync::Arc};
/// Complete immutable Cedar entity JSON source; SDK parsing and schema admission are separate.
#[derive(Debug, Clone, PartialEq)]
pub struct EntitySourceJson(Arc<Value>);
impl<'de> Deserialize<'de> for EntitySourceJson {
    fn deserialize<D: Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        Value::deserialize(decoder).map(|value| Self(Arc::new(value)))
    }
}
impl Serialize for EntitySourceJson {
    fn serialize<S: Serializer>(&self, encoder: S) -> Result<S::Ok, S::Error> {
        self.0.as_ref().serialize(encoder)
    }
}
impl Deref for EntitySourceJson {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
