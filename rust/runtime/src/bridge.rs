//! Policy parsing, source verification and individual Cedar case execution.
use crate::entities::EntitySlot;
use crate::input::{Case, Manifest, valid_revision_name};
use crate::observation::ReplayMetrics;
use crate::policy_codec::{load_policy_set, policy_bodies_by_id, policy_body_counts};
use crate::preparation::{PreparedReplay, request_uid};
use crate::syntax::CheckedRevision;

use cedar_policy::{
    AuthorizationError, Authorizer, Context, Decision, EntityUid, PolicySet, Request,
};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::str::FromStr;
use std::time::Instant;

/// Replay Lean's requests against independently stored Cedar source files.
/// Cedar assigns source policy IDs, so bodies and diagnostics are compared
/// through policy bodies rather than regenerated IDs.
pub fn check_direct_sources(manifest: &Manifest, directory: &Path) -> Result<(), String> {
    if manifest.cases.is_empty() {
        return Err("manifest has no cases".into());
    }
    let mut sources = BTreeMap::new();
    let mut entities = EntitySlot::new(None);
    for case in &manifest.cases {
        let policies = direct_source(&mut sources, directory, case)?;
        check_direct_case(case, policies, &mut entities)
            .map_err(|error| format!("{}: {error}", case.name))?;
    }
    Ok(())
}

fn direct_source<'a>(
    sources: &'a mut BTreeMap<String, PolicySet>,
    directory: &Path,
    case: &Case,
) -> Result<&'a PolicySet, String> {
    if !valid_revision_name(&case.revision) {
        return Err(format!("{}: invalid revision name", case.name));
    }
    if !sources.contains_key(&case.revision) {
        let path = directory.join(format!("{}.cedar", case.revision));
        let text = std::fs::read_to_string(&path)
            .map_err(|error| format!("{}: {error}", path.display()))?;
        let policies =
            PolicySet::from_str(&text).map_err(|error| format!("{}: {error}", path.display()))?;
        sources.insert(case.revision.clone(), policies);
    }
    Ok(&sources[&case.revision])
}

fn check_direct_case<'input>(
    case: &'input Case,
    policies: &PolicySet,
    entity_slot: &mut EntitySlot<'_, 'input>,
) -> Result<(), String> {
    if policies.policies().count() != case.policy_ids.len() {
        return Err("direct policy count differs".into());
    }
    let compiled = load_policy_set(&case.policies)?;
    let direct_bodies = policy_bodies_by_id(policies)?;
    let compiled_bodies = policy_bodies_by_id(&compiled)?;
    let expected_ids = case.policy_ids.iter().cloned().collect::<BTreeSet<_>>();
    if expected_ids.len() != case.policy_ids.len()
        || expected_ids != compiled_bodies.keys().cloned().collect()
    {
        return Err("loaded policy IDs differ from the Lean compilation".into());
    }
    if policy_body_counts(&direct_bodies) != policy_body_counts(&compiled_bodies) {
        return Err("direct policy bodies differ".into());
    }
    let entities = entity_slot
        .get(&case.entities, None)
        .map_err(|error| format!("Cedar entities: {error}"))?;
    let uid = |value: &str| EntityUid::from_str(value).map_err(|error| error.to_string());
    let context = Context::from_json_value(case.request.context.clone(), None)
        .map_err(|error| format!("Cedar context: {error}"))?;
    let request = Request::new(
        uid(&case.request.principal)?,
        uid(&case.request.action)?,
        uid(&case.request.resource)?,
        context,
        None,
    )
    .map_err(|error| format!("Cedar request: {error}"))?;
    let response = Authorizer::new().is_authorized(&request, policies, entities);
    let decision = match response.decision() {
        Decision::Allow => "allow",
        Decision::Deny => "deny",
    };
    let reasons = diagnostic_body_counts(
        response.diagnostics().reason().map(ToString::to_string),
        &direct_bodies,
    )?;
    let expected_reasons =
        diagnostic_body_counts(case.expected_reasons.iter().cloned(), &compiled_bodies)?;
    let errors = diagnostic_body_counts(
        response.diagnostics().errors().map(|error| match error {
            AuthorizationError::PolicyEvaluationError(error) => error.policy_id().to_string(),
        }),
        &direct_bodies,
    )?;
    let expected_errors = diagnostic_body_counts(
        case.expected_error_policies.iter().cloned(),
        &compiled_bodies,
    )?;
    if decision != case.expected || reasons != expected_reasons || errors != expected_errors {
        return Err(format!(
            "direct Cedar expected {} reasons {:?} errors {:?}, got {} reasons {:?} errors {:?}",
            case.expected, expected_reasons, expected_errors, decision, reasons, errors,
        ));
    }
    Ok(())
}

fn diagnostic_body_counts(
    ids: impl IntoIterator<Item = String>,
    bodies: &BTreeMap<String, String>,
) -> Result<BTreeMap<&str, usize>, String> {
    let mut counts = BTreeMap::new();
    let mut seen = BTreeSet::new();
    for id in ids {
        if !seen.insert(id.clone()) {
            return Err(format!("duplicate diagnostic policy ID: {id}"));
        }
        let body = bodies
            .get(&id)
            .ok_or_else(|| format!("unknown diagnostic policy ID: {id}"))?;
        *counts.entry(body.as_str()).or_insert(0) += 1;
    }
    Ok(counts)
}

pub(crate) struct ObservedDecision {
    pub(crate) decision: String,
    pub(crate) reasons: Vec<String>,
    pub(crate) error_policy_ids: Vec<String>,
}

pub(crate) fn check_case<'input>(
    case: &'input Case,
    revision: &CheckedRevision,
    entity_slot: &mut EntitySlot<'_, 'input>,
    mut metrics: Option<&mut ReplayMetrics>,
    mut preparation: Option<&mut PreparedReplay>,
) -> Result<ObservedDecision, String> {
    let CheckedRevision {
        policies,
        rendered,
        compiled_bodies,
        rendered_bodies,
        ..
    } = revision;
    let schema = entity_slot.schema();
    let started = metrics.as_ref().map(|_| Instant::now());
    let expected_ids = case
        .policy_ids
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if expected_ids.len() != case.policy_ids.len()
        || !expected_ids
            .into_iter()
            .eq(compiled_bodies.keys().map(String::as_str))
    {
        return Err("loaded policy IDs differ from the Lean compilation".into());
    }
    let entities = entity_slot
        .get(&case.entities, metrics.as_deref_mut())
        .map_err(|error| format!("Cedar schema entities: {error}"))?;
    let action = request_uid(
        &case.request.action,
        &mut preparation,
        metrics.as_deref_mut(),
    )?;
    let context = Context::from_json_value(
        case.request.context.clone(),
        schema.map(|checked| (checked, &action)),
    )
    .map_err(|error| format!("Cedar schema context: {error}"))?;
    let request = Request::new(
        request_uid(
            &case.request.principal,
            &mut preparation,
            metrics.as_deref_mut(),
        )?,
        action,
        request_uid(
            &case.request.resource,
            &mut preparation,
            metrics.as_deref_mut(),
        )?,
        context,
        schema,
    )
    .map_err(|error| format!("Cedar schema request: {error}"))?;
    if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
        let elapsed = started.elapsed().as_nanos();
        stats.runtime_preparation_ns += elapsed;
        stats.request_preparation_ns += elapsed;
    }
    let started = metrics.as_ref().map(|_| Instant::now());
    let response = Authorizer::new().is_authorized(&request, policies, entities);
    if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
        stats.authorization_ns += started.elapsed().as_nanos();
        stats.authorization_calls += 1;
    }
    let diagnostic_start = metrics.as_ref().map(|_| Instant::now());
    let decision = match response.decision() {
        Decision::Allow => "allow",
        Decision::Deny => "deny",
    };
    let reasons = response
        .diagnostics()
        .reason()
        .map(ToString::to_string)
        .collect::<BTreeSet<_>>();
    let error_policies = response
        .diagnostics()
        .errors()
        .map(|error| match error {
            AuthorizationError::PolicyEvaluationError(error) => error.policy_id().to_string(),
        })
        .collect::<BTreeSet<_>>();
    let expected_reasons = case
        .expected_reasons
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let expected_error_policies = case
        .expected_error_policies
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    if decision != case.expected
        || reasons != expected_reasons
        || error_policies != expected_error_policies
        || expected_reasons.len() != case.expected_reasons.len()
        || expected_error_policies.len() != case.expected_error_policies.len()
    {
        return Err(format!(
            "expected {} reasons {:?} errors {:?}, got {} reasons {:?} errors {:?}",
            case.expected,
            expected_reasons,
            expected_error_policies,
            decision,
            reasons,
            error_policies
        ));
    }
    if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), diagnostic_start) {
        stats.diagnostics_ns += started.elapsed().as_nanos();
    }
    let started = metrics.as_ref().map(|_| Instant::now());
    let reparsed = Authorizer::new().is_authorized(&request, rendered, entities);
    if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
        stats.authorization_ns += started.elapsed().as_nanos();
        stats.authorization_calls += 1;
    }
    let diagnostic_start = metrics.as_ref().map(|_| Instant::now());
    let rendered_reasons = diagnostic_body_counts(
        reparsed.diagnostics().reason().map(ToString::to_string),
        rendered_bodies,
    )?;
    let compiled_reasons = diagnostic_body_counts(reasons.iter().cloned(), compiled_bodies)?;
    let rendered_errors = diagnostic_body_counts(
        reparsed.diagnostics().errors().map(|error| match error {
            AuthorizationError::PolicyEvaluationError(error) => error.policy_id().to_string(),
        }),
        rendered_bodies,
    )?;
    let compiled_errors = diagnostic_body_counts(error_policies.iter().cloned(), compiled_bodies)?;
    if reparsed.decision() != response.decision()
        || rendered_reasons != compiled_reasons
        || rendered_errors != compiled_errors
    {
        return Err("rendered Cedar text changed authorization diagnostics".into());
    }
    if let (Some(stats), Some(started)) = (metrics, diagnostic_start) {
        stats.diagnostics_ns += started.elapsed().as_nanos();
    }
    Ok(ObservedDecision {
        decision: decision.into(),
        reasons: reasons.into_iter().collect(),
        error_policy_ids: error_policies.into_iter().collect(),
    })
}

#[cfg(test)]
#[path = "../tests/unit/bridge.rs"]
mod tests;
