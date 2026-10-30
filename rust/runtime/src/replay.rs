//! Canonical revision preparation, ordered replay and optional observations.
use std::ops::Deref;

use crate::bridge::{
    Case, CheckedRevision, Manifest, ReplayReceipt, SourcePolicies, check_case, json_sha256,
    valid_revision_name,
};
use crate::canonical::value_sha256;
use crate::entities::EntitySlot;
use crate::observation::ReplayMetrics;
use cedar_policy::Schema;
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;
/// Measure the same replay implementation used by ordinary conformance.
pub fn replay_manifest_measured(
    manifest: &Manifest,
    metrics: &mut ReplayMetrics,
) -> Result<Vec<ReplayReceipt>, String> {
    check_manifest_observed(&manifest.cases, true, None, Some(metrics))
}

/// Reject empty bundles, parse every policy set, and compare every decision.
pub fn check_manifest(manifest: &Manifest) -> Result<(), String> {
    check_manifest_inner(&manifest.cases, false, None).map(|_| ())
}

/// Check Lean's manifest against Cedar and return content-bound replay records.
pub fn replay_manifest(manifest: &Manifest) -> Result<Vec<ReplayReceipt>, String> {
    check_manifest_inner(&manifest.cases, true, None)
}

pub(crate) fn check_manifest_inner(
    cases: &[Case],
    collect_receipts: bool,
    schema: Option<&Schema>,
) -> Result<Vec<ReplayReceipt>, String> {
    check_manifest_observed(cases, collect_receipts, schema, None)
}

pub(crate) fn check_manifest_observed(
    cases: &[Case],
    collect_receipts: bool,
    schema: Option<&Schema>,
    metrics: Option<&mut ReplayMetrics>,
) -> Result<Vec<ReplayReceipt>, String> {
    check_manifest_prepared(cases, collect_receipts, schema, metrics, BTreeMap::new())
}

// Prepared policies belong only to this invocation and its already checked schema.
// All schema validation completes before this function observes any request.
pub(crate) fn check_manifest_prepared(
    cases: &[Case],
    collect_receipts: bool,
    schema: Option<&Schema>,
    metrics: Option<&mut ReplayMetrics>,
    loaded: BTreeMap<String, SourcePolicies>,
) -> Result<Vec<ReplayReceipt>, String> {
    check_manifest_with_entities(
        cases,
        collect_receipts,
        metrics,
        loaded,
        EntitySlot::new(schema),
    )
}

pub(crate) fn check_manifest_with_entities<'input>(
    cases: &'input [Case],
    collect_receipts: bool,
    mut metrics: Option<&mut ReplayMetrics>,
    mut loaded: BTreeMap<String, SourcePolicies>,
    mut entities: EntitySlot<'_, 'input>,
) -> Result<Vec<ReplayReceipt>, String> {
    if cases.is_empty() {
        return Err("manifest has no cases".into());
    }
    let mut names = BTreeSet::new();
    let mut revisions = BTreeMap::new();
    let mut receipts = if collect_receipts {
        Vec::with_capacity(cases.len())
    } else {
        Vec::new()
    };
    for case in cases {
        if !valid_revision_name(&case.revision) {
            return Err(format!("{}: invalid revision name", case.name));
        }
        if !names.insert(&case.name) {
            return Err(format!("duplicate case name: {}", case.name));
        }
        if !revisions.contains_key(&case.revision) {
            let started = metrics.as_ref().map(|_| Instant::now());
            let checked = match loaded.remove(&case.revision) {
                Some(policies) => policies.checked(case, collect_receipts),
                None => {
                    if let Some(stats) = metrics.as_deref_mut() {
                        stats.source_policy_loads += 1;
                    }
                    CheckedRevision::new(case, collect_receipts)
                }
            }
            .map_err(|error| format!("{}: {error}", case.name))?;
            if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
                let elapsed = started.elapsed().as_nanos();
                stats.runtime_preparation_ns += elapsed;
                stats.revision_preparation_ns += elapsed;
                stats.prepared_revisions += 1;
            }
            revisions.insert(case.revision.clone(), checked);
        }
        let revision = &revisions[&case.revision];
        if revision.source != *case.policies.deref() {
            return Err(format!("{}: conflicting revision output", case.revision));
        }
        let observed = check_case(case, revision, &mut entities, metrics.as_deref_mut())
            .map_err(|error| format!("{}: {error}", case.name))?;
        if collect_receipts {
            let started = metrics.as_ref().map(|_| Instant::now());
            let error_free_allow =
                observed.decision == "allow" && observed.error_policy_ids.is_empty();
            receipts.push(ReplayReceipt {
                format_version: 1,
                cedar_policy_version: cedar_policy::get_sdk_version().to_string(),
                cedar_language_version: cedar_policy::get_lang_version().to_string(),
                case_name: case.name.clone(),
                revision: case.revision.clone(),
                policies_sha256: revision
                    .policy_sha256
                    .as_ref()
                    .ok_or("missing policy digest for replay receipt")?
                    .clone(),
                entities_sha256: value_sha256(&case.entities)?,
                request_sha256: json_sha256(&case.request)?,
                decision: observed.decision,
                reasons: observed.reasons,
                error_policy_ids: observed.error_policy_ids,
                error_free_allow,
            });
            if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
                stats.receipt_ns += started.elapsed().as_nanos();
            }
        }
    }
    Ok(receipts)
}

/// Recompute official Cedar decisions and reject any drift from stored records.
/// The caller must authenticate the stored records separately.
pub fn verify_replay_receipts(
    manifest: &Manifest,
    receipts: &[ReplayReceipt],
) -> Result<(), String> {
    if replay_manifest(manifest)? != receipts {
        return Err("Cedar replay receipts differ from the current manifest or runtime".into());
    }
    Ok(())
}
