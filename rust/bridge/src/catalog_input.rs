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

pub(crate) struct Document<'a> {
    pub sources: cedar_poo_runtime::CatalogSources,
    pub entries: BTreeMap<String, &'a str>,
}
pub(crate) fn fields(input: &str) -> BTreeMap<String, &str> {
    spans::object(input).unwrap_or_default()
}
pub(crate) fn document(input: &str) -> Result<Document<'_>, String> {
    // Preserve complete syntax/number/depth errors before transport or SDK checks.
    let raw = decode(input)?;
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Envelope {
        format_version: u32,
        sources: serde::de::IgnoredAny,
        entries: UniqueNames,
    }
    let header: Envelope = serde_json::from_str(input).map_err(|e| e.to_string())?;
    if header.format_version != 2 {
        return Err("unsupported catalog format version".into());
    }
    let _ = (header.sources, header.entries);
    let sources: cedar_poo_runtime::CatalogSources =
        serde_json::from_str(raw["sources"]).map_err(|e| e.to_string())?;
    sources.check_unique()?;
    Ok(Document {
        sources,
        entries: decode(raw["entries"])?,
    })
}
struct UniqueNames;
impl<'de> Deserialize<'de> for UniqueNames {
    fn deserialize<D: Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        struct Names;
        impl<'de> Visitor<'de> for Names {
            type Value = UniqueNames;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("unique catalog entry names")
            }
            fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<UniqueNames, A::Error> {
                let mut names = std::collections::BTreeSet::new();
                while let Some(name) = map.next_key::<String>()? {
                    if !names.insert(name) {
                        return Err(de::Error::custom("duplicate catalog entry"));
                    }
                    map.next_value::<serde::de::IgnoredAny>()?;
                }
                Ok(UniqueNames)
            }
        }
        decoder.deserialize_map(Names)
    }
}

pub(crate) fn is_schema_bound(fields: &BTreeMap<String, &str>) -> bool {
    fields
        .get("manifest_kind")
        .and_then(|raw| serde_json::from_str::<String>(raw).ok())
        .is_some_and(|kind| kind == "schema-bound")
}
