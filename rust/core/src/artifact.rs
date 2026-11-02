//! Small, Cedar-independent representation of a compiled Lean policy set.

use crate::JsonSourceIdentity;
use serde::Deserialize;
use serde_json::Value;
use std::{
    ops::Deref,
    str::FromStr,
    sync::{Arc, OnceLock},
};

/// Materialized Cedar policy set in the public JSON policy-set format.
#[derive(Debug, Clone)]
pub struct CompiledPolicyJson(Arc<JsonSource>);
#[derive(Debug)]
struct JsonSource {
    value: Value,
    identity: OnceLock<Result<String, String>>,
}

impl<'de> Deserialize<'de> for CompiledPolicyJson {
    fn deserialize<D: serde::Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        Value::deserialize(decoder).map(|value| {
            Self(Arc::new(JsonSource {
                value,
                identity: OnceLock::new(),
            }))
        })
    }
}

/// Cedar source with static policies, editable templates, and links.
#[derive(Debug, Deserialize)]
#[serde(transparent)]
pub struct TemplateSourceJson(Value);

impl FromStr for CompiledPolicyJson {
    type Err = serde_json::Error;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        serde_json::from_str(source)
    }
}

impl CompiledPolicyJson {
    /// Immutable canonical-source identity, including floating-point signed zero.
    pub fn same_source(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0.value.same_source(&other.0.value)
    }
    /// Memoized complete JSON representation for source lookup, never admission.
    pub fn source_identity(&self) -> Result<&str, String> {
        self.0
            .identity
            .get_or_init(|| serde_json::to_string(&self.0.value).map_err(|e| e.to_string()))
            .as_ref()
            .map(String::as_str)
            .map_err(Clone::clone)
    }
    /// Serialize the artifact for storage or an application-owned Cedar parser.
    pub fn to_json_string(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(&self.0.value)
    }
}

impl FromStr for TemplateSourceJson {
    type Err = serde_json::Error;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        serde_json::from_str(source)
    }
}

impl TemplateSourceJson {
    /// Serialize Cedar source for storage or a Cedar parser.
    pub fn to_json_string(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(&self.0)
    }
}

// Borrowing the policy JSON preserves its wire shape; it performs no admission.
impl Deref for CompiledPolicyJson {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        &self.0.value
    }
}

impl Deref for TemplateSourceJson {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Raw immutable schema JSON at the SDK boundary; parsing this wrapper does not
/// establish schema validity, policy validation or request admission.
#[derive(Debug, Clone)]
pub struct SchemaSourceJson(Arc<JsonSource>);
impl<'de> Deserialize<'de> for SchemaSourceJson {
    fn deserialize<D: serde::Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        Value::deserialize(decoder).map(|value| {
            Self(Arc::new(JsonSource {
                value,
                identity: OnceLock::new(),
            }))
        })
    }
}
impl SchemaSourceJson {
    /// Complete immutable source identity, shared with every clone. Never admission.
    pub fn source_identity(&self) -> Result<&str, String> {
        self.0
            .identity
            .get_or_init(|| self.0.value.encode_source())
            .as_ref()
            .map(String::as_str)
            .map_err(Clone::clone)
    }
    /// Pointer equality is sufficient only for the same immutable source owner.
    pub fn same_source(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0.value.same_source(&other.0.value)
    }
}
impl Deref for SchemaSourceJson {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        &self.0.value
    }
}

#[cfg(test)]
#[path = "../tests/unit/schema_source.rs"]
mod schema_source_tests;
