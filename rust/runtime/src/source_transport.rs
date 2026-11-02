//! Bulk source-table wire contracts. Full sources are owned once, never admission.
use crate::{Case, Manifest, RequestInput, SchemaEvolutionBundle, ValidatedManifest};
use cedar_poo_core::{CompiledPolicyJson, EntitySourceJson, JsonSourceIdentity, SchemaSourceJson};
use serde::Deserialize;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet, HashSet, hash_map::RandomState};
use std::hash::{BuildHasher, Hash, Hasher};
use std::ops::Deref;

// Ordered structural fingerprinting allocates no encoded JSON. Fingerprints
// only select candidates; full exact source equality always decides uniqueness.
fn hash_source(value: &Value, state: &mut impl Hasher) {
    match value {
        Value::Null => state.write_u8(0),
        Value::Bool(v) => {
            state.write_u8(1);
            v.hash(state);
        }
        Value::Number(v) => {
            state.write_u8(2);
            v.hash(state);
        }
        Value::String(v) => {
            state.write_u8(3);
            v.hash(state);
        }
        Value::Array(items) => {
            state.write_u8(4);
            items.len().hash(state);
            for item in items {
                hash_source(item, state);
            }
        }
        Value::Object(fields) => {
            state.write_u8(5);
            fields.len().hash(state);
            for (key, value) in fields {
                key.hash(state);
                hash_source(value, state);
            }
        }
    }
}
struct EntitySourceKey<'a> {
    source: &'a Value,
    fingerprint: u64,
}
impl PartialEq for EntitySourceKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.source.same_source(other.source)
    }
}
impl Eq for EntitySourceKey<'_> {}
impl Hash for EntitySourceKey<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.fingerprint.hash(state);
    }
}
fn unique_entities_by(
    sources: &[EntitySourceJson],
    fingerprint: impl Fn(&Value) -> u64,
) -> Result<(), String> {
    let mut index = HashSet::with_capacity(sources.len());
    for source in sources {
        let value = source.deref();
        if !index.insert(EntitySourceKey {
            source: value,
            fingerprint: fingerprint(value),
        }) {
            return Err("duplicate source definition".into());
        }
    }
    Ok(())
}

/// Kind-separated complete bulk sources; resolving a reference performs no Cedar admission.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CatalogSources {
    policies: Vec<CompiledPolicyJson>,
    entities: Vec<EntitySourceJson>,
    schemas: Vec<SchemaSourceJson>,
}
#[derive(Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(transparent)]
struct PolicyRef(usize);
#[derive(Deserialize)]
#[serde(transparent)]
struct EntityRef(usize);
#[derive(Deserialize)]
#[serde(transparent)]
struct SchemaRef(usize);
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CaseReference {
    name: String,
    revision: String,
    policy_ids: Vec<String>,
    policy_ref: PolicyRef,
    entities_ref: EntityRef,
    request: RequestInput,
    expected: String,
    expected_reasons: Vec<String>,
    expected_error_policies: Vec<String>,
}
#[derive(Deserialize)]
enum RawKind {
    #[serde(rename = "raw")]
    Raw,
}
#[derive(Deserialize)]
enum SchemaKind {
    #[serde(rename = "schema-bound")]
    SchemaBound,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ManifestReference {
    manifest_kind: RawKind,
    cases: Vec<CaseReference>,
    #[serde(deserialize_with = "bindings")]
    revision_sources: BTreeMap<String, PolicyRef>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ValidatedReference {
    manifest_kind: SchemaKind,
    cases: Vec<CaseReference>,
    #[serde(deserialize_with = "bindings")]
    revision_sources: BTreeMap<String, PolicyRef>,
    schema_ref: SchemaRef,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct EvolutionReference {
    before: ValidatedReference,
    after: ValidatedReference,
}
fn bindings<'de, D: serde::Deserializer<'de>>(
    decoder: D,
) -> Result<BTreeMap<String, PolicyRef>, D::Error> {
    struct Unique;
    impl<'de> serde::de::Visitor<'de> for Unique {
        type Value = BTreeMap<String, PolicyRef>;
        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.write_str("unique revision source bindings")
        }
        fn visit_map<A: serde::de::MapAccess<'de>>(
            self,
            mut map: A,
        ) -> Result<Self::Value, A::Error> {
            let mut output = BTreeMap::new();
            while let Some((name, reference)) = map.next_entry::<String, PolicyRef>()? {
                if output.insert(name, reference).is_some() {
                    return Err(serde::de::Error::custom("duplicate revision binding"));
                }
            }
            Ok(output)
        }
    }
    decoder.deserialize_map(Unique)
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ArtifactReference {
    root: String,
    policy_ref: PolicyRef,
}
/// A named immutable policy publication resolved against its containing source table.
pub struct ResolvedPolicyArtifact {
    /// Publication name, still subject to the application's topology checks.
    pub root: String,
    /// Complete source snapshot; neither SDK validation nor authority is inferred.
    pub policies: CompiledPolicyJson,
}
impl CatalogSources {
    /// Project only complete policy sources used by actual cases. No SDK parsing
    /// or revision admission is performed; malformed references remain replay errors.
    pub fn policy_sources(&self, input: &str) -> Result<Vec<CompiledPolicyJson>, String> {
        #[derive(Deserialize)]
        struct Row {
            policy_ref: PolicyRef,
        }
        #[derive(Deserialize)]
        struct Projection {
            cases: Vec<Row>,
        }
        let projection: Projection = serde_json::from_str(input).map_err(|e| e.to_string())?;
        let indices = projection
            .cases
            .into_iter()
            .map(|c| c.policy_ref.0)
            .collect::<BTreeSet<_>>();
        indices
            .into_iter()
            .map(|i| {
                self.policies
                    .get(i)
                    .cloned()
                    .ok_or_else(|| "policy reference out of bounds".to_owned())
            })
            .collect()
    }

    /// Enforce source-table canonicality without moving SDK admission ahead of replay.
    pub fn check_unique(&self) -> Result<(), String> {
        fn unique<T: Ord>(
            sources: impl IntoIterator<Item = Result<T, String>>,
        ) -> Result<(), String> {
            let mut seen = BTreeSet::new();
            for source in sources {
                if !seen.insert(source?) {
                    return Err("duplicate source definition".into());
                }
            }
            Ok(())
        }
        unique(self.policies.iter().map(|v| v.source_identity()))?;
        let seed = RandomState::new();
        unique_entities_by(&self.entities, |source| {
            let mut state = seed.build_hasher();
            hash_source(source, &mut state);
            state.finish()
        })?;
        unique(self.schemas.iter().map(|v| v.source_identity()))?;
        Ok(())
    }
    fn cases(
        &self,
        cases: Vec<CaseReference>,
        bindings: BTreeMap<String, PolicyRef>,
    ) -> Result<Vec<Case>, String> {
        for reference in bindings.values() {
            self.policies
                .get(reference.0)
                .ok_or("revision policy reference out of bounds")?;
        }
        cases
            .into_iter()
            .map(|case| {
                if bindings.get(&case.revision) != Some(&case.policy_ref) {
                    return Err("case/revision source binding mismatch".into());
                }
                Ok(Case {
                    name: case.name,
                    revision: case.revision,
                    policy_ids: case.policy_ids,
                    policies: self
                        .policies
                        .get(case.policy_ref.0)
                        .ok_or("policy reference out of bounds")?
                        .clone(),
                    entities: self
                        .entities
                        .get(case.entities_ref.0)
                        .ok_or("entity reference out of bounds")?
                        .clone(),
                    request: case.request,
                    expected: case.expected,
                    expected_reasons: case.expected_reasons,
                    expected_error_policies: case.expected_error_policies,
                })
            })
            .collect()
    }
    /// Resolve raw manifest references against this exact immutable source table.
    pub fn manifest(&self, input: &str) -> Result<Manifest, String> {
        let raw: ManifestReference = serde_json::from_str(input).map_err(|e| e.to_string())?;
        let _ = raw.manifest_kind;
        Ok(Manifest {
            cases: self.cases(raw.cases, raw.revision_sources)?,
        })
    }
    fn validated(&self, raw: ValidatedReference) -> Result<ValidatedManifest, String> {
        let _ = raw.manifest_kind;
        Ok(ValidatedManifest {
            schema: self
                .schemas
                .get(raw.schema_ref.0)
                .ok_or("schema reference out of bounds")?
                .clone(),
            cases: self.cases(raw.cases, raw.revision_sources)?,
        })
    }
    /// Resolve schema-bound references; the caller still runs strict SDK validation.
    pub fn validated_manifest(&self, input: &str) -> Result<ValidatedManifest, String> {
        self.validated(serde_json::from_str(input).map_err(|e| e.to_string())?)
    }
    /// Resolve both independently replayed schema-evolution projections.
    pub fn evolution(&self, input: &str) -> Result<SchemaEvolutionBundle, String> {
        let raw: EvolutionReference = serde_json::from_str(input).map_err(|e| e.to_string())?;
        Ok(SchemaEvolutionBundle {
            before: self.validated(raw.before)?,
            after: self.validated(raw.after)?,
        })
    }
    /// Resolve named source publications; application topology and SDK checks remain mandatory.
    pub fn policy_artifacts(&self, input: &str) -> Result<Vec<ResolvedPolicyArtifact>, String> {
        let refs: Vec<ArtifactReference> =
            serde_json::from_str(input).map_err(|e| e.to_string())?;
        refs.into_iter()
            .map(|r| {
                Ok(ResolvedPolicyArtifact {
                    root: r.root,
                    policies: self
                        .policies
                        .get(r.policy_ref.0)
                        .ok_or("artifact policy reference out of bounds")?
                        .clone(),
                })
            })
            .collect()
    }
    /// Only metadata for finite lazy schema-use planning; no SDK parser is called.
    pub fn schema_source(&self, input: &str) -> Result<SchemaSourceJson, String> {
        #[derive(Deserialize)]
        struct Projection {
            schema_ref: SchemaRef,
        }
        let raw: Projection = serde_json::from_str(input).map_err(|e| e.to_string())?;
        self.schemas
            .get(raw.schema_ref.0)
            .cloned()
            .ok_or_else(|| "schema reference out of bounds".into())
    }
}

#[cfg(test)]
#[path = "../tests/unit/source_transport.rs"]
mod tests;
