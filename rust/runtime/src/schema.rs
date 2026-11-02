//! Strict Cedar schema validation and schema-bound replay records.
use crate::observation::ReplayMetrics;
use crate::preparation::PreparedReplay;
use crate::replay::check_manifest_prepared_using;

use crate::input::{Case, ReplayReceipt};
use crate::policy_codec::{load_policy_set, render_identified_policy_sources};
use crate::revision::SourcePolicies;
use cedar_policy::{Entities, Schema, ValidationMode, Validator};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

/// A schema-bearing manifest intended for admission as a deployment candidate.
#[derive(Debug, Deserialize)]
pub struct ValidatedManifest {
    pub schema: cedar_poo_core::SchemaSourceJson,
    #[serde(deserialize_with = "crate::input::cases")]
    pub cases: Vec<Case>,
}

/// Render identified sources from one schema-bearing case after strict Cedar
/// validation and schema-bound entity parsing. The receiver must validate
/// again after injecting any reserved request context.
pub fn render_validated_policy_sources(
    manifest: &ValidatedManifest,
    case_name: &str,
) -> Result<BTreeMap<String, String>, String> {
    let mut matches = manifest.cases.iter().filter(|case| case.name == case_name);
    let case = matches
        .next()
        .ok_or_else(|| format!("missing Cedar candidate case: {case_name}"))?;
    if matches.next().is_some() {
        return Err(format!("duplicate Cedar candidate case: {case_name}"));
    }
    let policies = load_policy_set(&case.policies)?;
    if policies.policies().next().is_none() {
        return Err("policy source candidate is empty".into());
    }
    let actual_ids = policies
        .policies()
        .map(|policy| policy.id().to_string())
        .collect::<BTreeSet<_>>();
    let declared_ids = case.policy_ids.iter().cloned().collect::<BTreeSet<_>>();
    if case.policy_ids.len() != declared_ids.len() || declared_ids != actual_ids {
        return Err("candidate policy IDs differ from the Lean compilation".into());
    }
    let schema = Schema::from_json_value((*manifest.schema).clone())
        .map_err(|error| format!("Cedar schema: {error}"))?;
    let validation = Validator::new(schema.clone()).validate(&policies, ValidationMode::Strict);
    if !validation.validation_passed() {
        return Err(format!(
            "Cedar strict policy validation failed: {validation:?}"
        ));
    }
    Entities::from_json_value((*case.entities).clone(), Some(&schema))
        .map_err(|error| format!("Cedar schema entities: {error}"))?;
    render_identified_policy_sources(&case.policies)
}

/// Two schema-checked projections of the same policies and concrete inputs.
#[derive(Debug, Deserialize)]
pub struct SchemaEvolutionBundle {
    pub before: ValidatedManifest,
    pub after: ValidatedManifest,
}

/// A Cedar replay bound to the exact schema used for strict validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SchemaBoundReceipt {
    pub schema_sha256: String,
    pub replay: ReplayReceipt,
}

/// Evidence that a schema edit preserved Cedar's observed results for these inputs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SchemaOnlyRevisionReceipt {
    pub before_schema_sha256: String,
    pub after_schema_sha256: String,
    pub replay: Vec<ReplayReceipt>,
}

/// Validate policies and replay with schema-parsed entities, context, and request.
pub fn replay_validated_manifest(
    manifest: &ValidatedManifest,
) -> Result<Vec<SchemaBoundReceipt>, String> {
    replay_validated_observed(manifest, None)
}

/// Observe strict schema preparation and the canonical schema-bound replay.
pub fn replay_validated_manifest_measured(
    manifest: &ValidatedManifest,
    metrics: &mut ReplayMetrics,
) -> Result<Vec<SchemaBoundReceipt>, String> {
    replay_validated_observed(manifest, Some(metrics))
}

fn replay_validated_observed(
    manifest: &ValidatedManifest,
    mut metrics: Option<&mut ReplayMetrics>,
) -> Result<Vec<SchemaBoundReceipt>, String> {
    let started = metrics.as_ref().map(|_| Instant::now());
    let prepared =
        crate::schema_preparation::PreparedSchema::parse(&manifest.schema, metrics.as_deref_mut())?;
    if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
        let elapsed = started.elapsed().as_nanos();
        stats.runtime_preparation_ns += elapsed;
        stats.schema_preparation_ns += elapsed;
    }
    replay_with_schema(manifest, &prepared, metrics)
}

pub(crate) fn replay_with_schema(
    manifest: &ValidatedManifest,
    prepared: &crate::schema_preparation::PreparedSchema,
    metrics: Option<&mut ReplayMetrics>,
) -> Result<Vec<SchemaBoundReceipt>, String> {
    replay_with_schema_using(manifest, prepared, metrics, &mut PreparedReplay::default())
}

pub(crate) fn replay_with_schema_using(
    manifest: &ValidatedManifest,
    prepared: &crate::schema_preparation::PreparedSchema,
    mut metrics: Option<&mut ReplayMetrics>,
    preparation: &mut PreparedReplay,
) -> Result<Vec<SchemaBoundReceipt>, String> {
    let started = metrics.as_ref().map(|_| Instant::now());
    let validator = &prepared.validator;
    let mut revisions = BTreeMap::new();
    for case in &manifest.cases {
        if !revisions.contains_key(&case.revision) {
            let policies =
                SourcePolicies::prepared(case, metrics.as_deref_mut(), Some(preparation))?;
            if let Some(stats) = metrics.as_deref_mut() {
                stats.policy_validation_calls += 1;
            }
            let result = validator.validate(policies.policies(), ValidationMode::Strict);
            if !result.validation_passed() {
                return Err(format!(
                    "{}: Cedar strict policy validation failed: {result:?}",
                    case.revision
                ));
            }
            revisions.insert(case.revision.clone(), policies);
        }
    }
    let schema_sha256 = prepared.digest()?.to_owned();
    if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
        let elapsed = started.elapsed().as_nanos();
        stats.runtime_preparation_ns += elapsed;
        stats.schema_preparation_ns += elapsed;
    }
    check_manifest_prepared_using(
        &manifest.cases,
        Some(validator.schema()),
        metrics,
        revisions,
        preparation,
    )
    .map(|receipts| {
        receipts
            .into_iter()
            .map(|replay| SchemaBoundReceipt {
                schema_sha256: schema_sha256.clone(),
                replay,
            })
            .collect()
    })
}

/// Recompute schema-bound receipts against the current official Cedar runtime.
pub fn verify_validated_replay_receipts(
    manifest: &ValidatedManifest,
    receipts: &[SchemaBoundReceipt],
) -> Result<(), String> {
    if replay_validated_manifest(manifest)? != receipts {
        return Err(
            "schema-bound Cedar receipts differ from the current manifest or runtime".into(),
        );
    }
    Ok(())
}

/// Replay the same policy and request artifacts under two different schemas.
/// Equality is restricted to the finite cases supplied by the caller.
pub fn replay_schema_only_revision(
    bundle: &SchemaEvolutionBundle,
) -> Result<SchemaOnlyRevisionReceipt, String> {
    let before = replay_validated_manifest(&bundle.before)?;
    let after = replay_validated_manifest(&bundle.after)?;
    let before_schema_sha256 = before
        .first()
        .ok_or("schema-only revision has no cases")?
        .schema_sha256
        .clone();
    let after_schema_sha256 = after
        .first()
        .ok_or("schema-only revision has no cases")?
        .schema_sha256
        .clone();
    if before_schema_sha256 == after_schema_sha256 {
        return Err("schema-only revision requires a changed schema".into());
    }
    let before_replay = before.into_iter().map(|row| row.replay).collect::<Vec<_>>();
    let after_replay = after.into_iter().map(|row| row.replay).collect::<Vec<_>>();
    if before_replay != after_replay {
        return Err(
            "schema-only revision changed policy/request artifacts or Cedar diagnostics".into(),
        );
    }
    Ok(SchemaOnlyRevisionReceipt {
        before_schema_sha256,
        after_schema_sha256,
        replay: before_replay,
    })
}

/// Recompute a stored schema-only revision receipt against the current runtime.
pub fn verify_schema_only_revision(
    bundle: &SchemaEvolutionBundle,
    receipt: &SchemaOnlyRevisionReceipt,
) -> Result<(), String> {
    if &replay_schema_only_revision(bundle)? != receipt {
        return Err(
            "schema-only revision receipt differs from the current inputs or runtime".into(),
        );
    }
    Ok(())
}

impl crate::schema_preparation::SchemaPreparation {
    /// Replay the exact schema source, strictly validating every revision afresh.
    pub fn replay(
        &mut self,
        manifest: &ValidatedManifest,
        metrics: Option<&mut ReplayMetrics>,
    ) -> Result<Vec<SchemaBoundReceipt>, String> {
        let mut metrics = metrics;
        let schema = self.acquire(&manifest.schema, metrics.as_deref_mut())?;
        replay_with_schema(manifest, &schema, metrics)
    }
}
