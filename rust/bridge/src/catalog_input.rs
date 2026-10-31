//! Validate the complete original JSON first; retain borrowed entry slices.
//!
//! The preflight uses serde's normal number/string/depth parser in original
//! input order. A linear boundary index then borrows entry spans; it makes no
//! syntax/admission decision. Entry Value decoding keeps last-wins normalization.
//! Enabling serde's raw_value feature would alter private-token Value semantics,
//! so the existing serde feature set is preserved.
use serde::de::{self, Deserialize, Deserializer, MapAccess, SeqAccess, Visitor};
use serde_json::Value;
use std::collections::BTreeMap;
use std::fmt;
#[path = "catalog_spans.rs"]
mod spans;

pub(crate) fn decode(input: &str) -> Result<BTreeMap<String, &str>, String> {
    let mut decoder = serde_json::Deserializer::from_str(input);
    Root::deserialize(&mut decoder)
        .and_then(|_| decoder.end())
        .map_err(|e| e.to_string())?;
    spans::object(input).ok_or_else(|| "validated catalog boundary unavailable".into())
}

struct Root;
impl<'de> Deserialize<'de> for Root {
    fn deserialize<D: Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        struct RootVisitor;
        impl<'de> Visitor<'de> for RootVisitor {
            type Value = Root;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a map")
            }
            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Root, M::Error> {
                while map.next_key::<String>()?.is_some() {
                    map.next_value::<Syntax>()?;
                }
                Ok(Root)
            }
        }
        decoder.deserialize_map(RootVisitor)
    }
}

struct Syntax;
impl<'de> Deserialize<'de> for Syntax {
    fn deserialize<D: Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        decoder.deserialize_any(SyntaxVisitor)
    }
}
struct SyntaxVisitor;
impl<'de> Visitor<'de> for SyntaxVisitor {
    type Value = Syntax;
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("any valid JSON value")
    }
    fn visit_unit<E: de::Error>(self) -> Result<Syntax, E> {
        Ok(Syntax)
    }
    fn visit_bool<E: de::Error>(self, _: bool) -> Result<Syntax, E> {
        Ok(Syntax)
    }
    fn visit_i64<E: de::Error>(self, _: i64) -> Result<Syntax, E> {
        Ok(Syntax)
    }
    fn visit_u64<E: de::Error>(self, _: u64) -> Result<Syntax, E> {
        Ok(Syntax)
    }
    fn visit_f64<E: de::Error>(self, _: f64) -> Result<Syntax, E> {
        Ok(Syntax)
    }
    fn visit_str<E: de::Error>(self, _: &str) -> Result<Syntax, E> {
        Ok(Syntax)
    }
    fn visit_seq<M: SeqAccess<'de>>(self, mut seq: M) -> Result<Syntax, M::Error> {
        while seq.next_element::<Syntax>()?.is_some() {}
        Ok(Syntax)
    }
    fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Syntax, M::Error> {
        while map.next_key::<SyntaxKey>()?.is_some() {
            map.next_value::<Syntax>()?;
        }
        Ok(Syntax)
    }
}

pub(crate) fn value(raw: &str) -> Result<Value, String> {
    serde_json::from_str(raw).map_err(|e| e.to_string())
}

#[cfg(test)]
#[path = "../tests/unit/catalog_input.rs"]
mod tests;

pub(crate) fn schema_sources(
    catalog: &BTreeMap<String, &str>,
) -> Vec<cedar_poo_core::SchemaSourceJson> {
    catalog
        .values()
        .filter_map(|raw| {
            let fields = spans::object(raw)?;
            fields.get("cases")?;
            serde_json::from_str(fields.get("schema")?).ok()
        })
        .collect()
}

struct SyntaxKey;
impl<'de> Deserialize<'de> for SyntaxKey {
    fn deserialize<D: Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        struct KeyVisitor;
        impl Visitor<'_> for KeyVisitor {
            type Value = SyntaxKey;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a string")
            }
            fn visit_str<E: de::Error>(self, _: &str) -> Result<SyntaxKey, E> {
                Ok(SyntaxKey)
            }
        }
        decoder.deserialize_str(KeyVisitor)
    }
}
