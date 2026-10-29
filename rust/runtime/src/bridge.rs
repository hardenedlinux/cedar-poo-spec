//! Parse official Cedar JSON and compare Rust authorization to Lean receipts.

use crate::{CompiledPolicyJson, TemplateSourceJson};
use cedar_policy::{
    AuthorizationError, Authorizer, Context, Decision, Entities, EntityUid, PolicySet, Request,
    Schema,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;
use std::path::Path;
use std::str::FromStr;
use std::time::Instant;

/// Optional observations of the canonical replay, excluding JSON transport and diagnostics.
/// Durations are observations, never authorization inputs or acceptance thresholds.
#[derive(Default, Debug, Serialize)]
pub struct ReplayMetrics {
    pub runtime_preparation_ns: u128,
    pub authorization_ns: u128,
    pub prepared_revisions: usize,
    pub authorization_calls: usize,
}

/// Measure the same replay implementation used by ordinary conformance.
pub fn replay_manifest_measured(
    manifest: &Manifest,
    metrics: &mut ReplayMetrics,
) -> Result<Vec<ReplayReceipt>, String> {
    check_manifest_observed(&manifest.cases, true, None, Some(metrics))
}

/// Request fields emitted from the Lean Cedar model.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct RequestInput {
    pub principal: String,
    pub action: String,
    pub resource: String,
    pub context: Value,
}

/// One concrete authorization case and its Lean-computed receipt.
#[derive(Debug, Clone, Deserialize)]
pub struct Case {
    pub name: String,
    pub revision: String,
    pub policy_ids: Vec<String>,
    pub policies: CompiledPolicyJson,
    pub entities: Value,
    pub request: RequestInput,
    pub expected: String,
    pub expected_reasons: Vec<String>,
    pub expected_error_policies: Vec<String>,
}

/// Bundle of Lean-computed cases for the official Cedar engine.
#[derive(Debug, Deserialize)]
pub struct Manifest {
    pub cases: Vec<Case>,
}

/// A reproducible record of one official Cedar replay, not a Lean proof or a signature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayReceipt {
    pub format_version: u32,
    pub cedar_policy_version: String,
    pub cedar_language_version: String,
    pub case_name: String,
    pub revision: String,
    pub policies_sha256: String,
    pub entities_sha256: String,
    pub request_sha256: String,
    pub decision: String,
    pub reasons: Vec<String>,
    pub error_policy_ids: Vec<String>,
    /// Conservative deployment signal; Cedar's decision remains recorded separately.
    pub error_free_allow: bool,
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
    mut metrics: Option<&mut ReplayMetrics>,
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
            let checked = CheckedRevision::new(case, collect_receipts)
                .map_err(|error| format!("{}: {error}", case.name))?;
            if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
                stats.runtime_preparation_ns += started.elapsed().as_nanos();
                stats.prepared_revisions += 1;
            }
            revisions.insert(case.revision.clone(), checked);
        }
        let revision = &revisions[&case.revision];
        if revision.source != *case.policies.deref() {
            return Err(format!("{}: conflicting revision output", case.revision));
        }
        let observed = check_case(
            case,
            &revision.policies,
            &revision.rendered,
            &revision.compiled_bodies,
            &revision.rendered_bodies,
            schema,
            metrics.as_deref_mut(),
        )
        .map_err(|error| format!("{}: {error}", case.name))?;
        if collect_receipts {
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
                entities_sha256: json_sha256(&case.entities)?,
                request_sha256: json_sha256(&case.request)?,
                decision: observed.decision,
                reasons: observed.reasons,
                error_policy_ids: observed.error_policy_ids,
                error_free_allow,
            });
        }
    }
    Ok(receipts)
}

fn valid_revision_name(revision: &str) -> bool {
    revision.split('.').all(|segment| {
        !segment.is_empty()
            && segment
                .chars()
                .all(|character| character.is_ascii_alphanumeric() || character == '-')
    })
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

pub(crate) fn json_sha256(value: &impl Serialize) -> Result<String, String> {
    let value = serde_json::to_value(value).map_err(|error| error.to_string())?;
    let mut bytes = Vec::new();
    write_canonical_json(&value, &mut bytes)?;
    let digest = Sha256::digest(bytes);
    Ok(digest.iter().map(|byte| format!("{byte:02x}")).collect())
}

fn write_canonical_json(value: &Value, output: &mut Vec<u8>) -> Result<(), String> {
    match value {
        Value::Null => output.extend_from_slice(b"null"),
        Value::Bool(value) => output.extend_from_slice(if *value { b"true" } else { b"false" }),
        Value::Number(value) => output.extend_from_slice(value.to_string().as_bytes()),
        Value::String(value) => {
            output.extend_from_slice(&serde_json::to_vec(value).map_err(|error| error.to_string())?)
        }
        Value::Array(values) => {
            output.push(b'[');
            for (index, value) in values.iter().enumerate() {
                if index > 0 {
                    output.push(b',');
                }
                write_canonical_json(value, output)?;
            }
            output.push(b']');
        }
        Value::Object(values) => {
            output.push(b'{');
            let mut entries = values.iter().collect::<Vec<_>>();
            entries.sort_unstable_by(|left, right| left.0.cmp(right.0));
            for (index, (key, value)) in entries.into_iter().enumerate() {
                if index > 0 {
                    output.push(b',');
                }
                output.extend_from_slice(
                    &serde_json::to_vec(key).map_err(|error| error.to_string())?,
                );
                output.push(b':');
                write_canonical_json(value, output)?;
            }
            output.push(b'}');
        }
    }
    Ok(())
}

struct CheckedRevision {
    source: Value,
    policy_sha256: Option<String>,
    policies: PolicySet,
    rendered: PolicySet,
    compiled_bodies: BTreeMap<String, String>,
    rendered_bodies: BTreeMap<String, String>,
}

impl CheckedRevision {
    fn new(case: &Case, hash_for_receipt: bool) -> Result<Self, String> {
        let policies = load_policy_set(&case.policies)?;
        let text = render_loaded_policy_set(&policies)?;
        let rendered = PolicySet::from_str(&text)
            .map_err(|error| format!("rendered Cedar text parse: {error}"))?;
        let compiled_bodies = policy_bodies_by_id(&policies)?;
        let rendered_bodies = policy_bodies_by_id(&rendered)?;
        if policy_body_counts(&compiled_bodies) != policy_body_counts(&rendered_bodies) {
            return Err("rendered Cedar text changed policy bodies".into());
        }
        Ok(Self {
            source: case.policies.deref().clone(),
            policy_sha256: if hash_for_receipt {
                Some(json_sha256(case.policies.deref())?)
            } else {
                None
            },
            policies,
            rendered,
            compiled_bodies,
            rendered_bodies,
        })
    }
}

/// Replay Lean's requests against independently stored Cedar source files.
/// Cedar assigns source policy IDs, so bodies and diagnostics are compared
/// through policy bodies rather than regenerated IDs.
pub fn check_direct_sources(manifest: &Manifest, directory: &Path) -> Result<(), String> {
    if manifest.cases.is_empty() {
        return Err("manifest has no cases".into());
    }
    let mut sources = BTreeMap::new();
    for case in &manifest.cases {
        let policies = direct_source(&mut sources, directory, case)?;
        check_direct_case(case, policies).map_err(|error| format!("{}: {error}", case.name))?;
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

fn check_direct_case(case: &Case, policies: &PolicySet) -> Result<(), String> {
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
    let entities = Entities::from_json_value(case.entities.clone(), None)
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
    let response = Authorizer::new().is_authorized(&request, policies, &entities);
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

fn policy_bodies_by_id(policies: &PolicySet) -> Result<BTreeMap<String, String>, String> {
    policies
        .policies()
        .map(|policy| Ok((policy.id().to_string(), canonical_policy_body(policy)?)))
        .collect()
}

fn policy_body_counts(bodies: &BTreeMap<String, String>) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for body in bodies.values() {
        *counts.entry(body.clone()).or_insert(0) += 1;
    }
    counts
}

fn diagnostic_body_counts(
    ids: impl IntoIterator<Item = String>,
    bodies: &BTreeMap<String, String>,
) -> Result<BTreeMap<String, usize>, String> {
    let mut counts = BTreeMap::new();
    let mut seen = BTreeSet::new();
    for id in ids {
        if !seen.insert(id.clone()) {
            return Err(format!("duplicate diagnostic policy ID: {id}"));
        }
        let body = bodies
            .get(&id)
            .ok_or_else(|| format!("unknown diagnostic policy ID: {id}"))?;
        *counts.entry(body.clone()).or_insert(0) += 1;
    }
    Ok(counts)
}

fn canonical_policy_body(policy: &cedar_policy::Policy) -> Result<String, String> {
    let json = policy
        .to_json()
        .map_err(|error| format!("Cedar policy JSON: {error}"))?;
    let normalized = cedar_policy::Policy::from_json(None, json)
        .map_err(|error| format!("Cedar policy normalization: {error}"))?;
    normalized
        .to_cedar()
        .ok_or_else(|| "normalized Cedar policy has no source".into())
}

/// Load a Lean-POO compiled policy set through Cedar's public JSON parser.
pub fn load_policy_set(json: &CompiledPolicyJson) -> Result<PolicySet, String> {
    let object = json
        .deref()
        .as_object()
        .ok_or("compiled policy artifact must be a JSON object")?;
    let static_policies = object
        .get("staticPolicies")
        .and_then(Value::as_object)
        .ok_or("compiled policy artifact needs staticPolicies")?;
    if !object
        .get("templates")
        .and_then(Value::as_object)
        .is_some_and(serde_json::Map::is_empty)
        || !object
            .get("templateLinks")
            .and_then(Value::as_array)
            .is_some_and(Vec::is_empty)
    {
        return Err("compiled policy artifact must contain only materialized policies".into());
    }
    let policies = PolicySet::from_json_value(json.deref().clone())
        .map_err(|error| format!("Cedar policy parse: {error}"))?;
    let expected = static_policies.keys().cloned().collect::<BTreeSet<_>>();
    let loaded = policies
        .policies()
        .map(|policy| policy.id().to_string())
        .collect::<BTreeSet<_>>();
    if expected != loaded {
        return Err("Cedar loaded a different policy ID set".into());
    }
    Ok(policies)
}

/// Load editable templates and links through Cedar's official parser.
pub fn load_template_source(source: &TemplateSourceJson) -> Result<PolicySet, String> {
    let linked = PolicySet::from_json_value(source.deref().clone())
        .map_err(|error| format!("Cedar template source parse: {error}"))?;
    if linked.templates().next().is_none() {
        return Err("source has no Cedar templates".into());
    }
    Ok(linked)
}

/// Compare the linked Cedar source with Lean's separately exported
/// materialized policy set, preserving policy IDs.
pub fn check_template_source(
    source: &TemplateSourceJson,
    materialized: &CompiledPolicyJson,
) -> Result<(), String> {
    let linked = load_template_source(source)?;
    let expected = load_policy_set(materialized)?;
    let linked_template_ids = linked
        .policies()
        .filter_map(|policy| policy.template_id().map(ToString::to_string))
        .collect::<BTreeSet<_>>();
    for template in linked.templates() {
        if !linked_template_ids.contains(&template.id().to_string()) {
            return Err(format!(
                "Cedar template has no linked policy: {}",
                template.id()
            ));
        }
    }
    let linked_policies = linked
        .policies()
        .map(|policy| -> Result<(String, String), String> {
            Ok((policy.id().to_string(), canonical_policy_body(policy)?))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    let expected_policies = expected
        .policies()
        .map(|policy| -> Result<(String, String), String> {
            Ok((policy.id().to_string(), canonical_policy_body(policy)?))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    if linked_policies.len() != linked.policies().count()
        || expected_policies.len() != expected.policies().count()
        || linked_policies != expected_policies
    {
        return Err("Cedar template links differ from Lean materialization".into());
    }
    Ok(())
}

/// Render an already admitted Cedar policy set without parsing JSON again.
pub fn render_loaded_policy_set(policies: &PolicySet) -> Result<String, String> {
    if policies.templates().next().is_some() {
        return Err("template source cannot render as a materialized policy file".into());
    }
    let mut rendered = policies
        .policies()
        .map(|policy| {
            let body = policy
                .to_cedar()
                .ok_or_else(|| "linked policy cannot render as Cedar text".to_owned())?;
            Ok((policy.id().to_string(), body))
        })
        .collect::<Result<Vec<_>, String>>()?;
    rendered.sort_by(|left, right| left.0.cmp(&right.0));
    let sections = rendered
        .into_iter()
        .map(|(id, body)| format!("// POO policy ID: {id}\n{body}"))
        .collect::<Vec<_>>();
    Ok(format!(
        "// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.\n{}\n",
        sections.join("\n\n")
    ))
}

/// Render a compiled Lean policy set to a valid `.cedar` source file.
/// Cedar source comments retain the original IDs for readers.
pub fn render_policy_source(json: &CompiledPolicyJson) -> Result<String, String> {
    render_loaded_policy_set(&load_policy_set(json)?)
}

/// Render individually identified Cedar sources for a Rust authority that
/// accepts one source and explicit policy ID per entry. The full-file renderer
/// only preserves IDs in comments; it is not suitable for that handoff.
pub fn render_identified_policy_sources(
    json: &CompiledPolicyJson,
) -> Result<BTreeMap<String, String>, String> {
    let policies = load_policy_set(json)?;
    let mut sources = BTreeMap::new();
    for policy in policies.policies() {
        let id = policy.id().to_string();
        let source = policy
            .to_cedar()
            .ok_or_else(|| format!("{id}: linked policy cannot render as Cedar text"))?;
        let reparsed = cedar_policy::Policy::parse(Some(policy.id().clone()), &source)
            .map_err(|error| format!("{id}: rendered Cedar policy parse: {error}"))?;
        let expected = policy
            .to_json()
            .map_err(|error| format!("{id}: Cedar policy JSON: {error}"))?;
        let actual = reparsed
            .to_json()
            .map_err(|error| format!("{id}: rendered Cedar policy JSON: {error}"))?;
        if expected != actual || reparsed.id() != policy.id() {
            return Err(format!(
                "{id}: rendered Cedar policy changed identity or body"
            ));
        }
        if sources.insert(id.clone(), source).is_some() {
            return Err(format!("duplicate rendered Cedar policy ID: {id}"));
        }
    }
    Ok(sources)
}

/// Render each revision to Cedar's human-readable policy language.
/// The original IDs remain in the JSON export; Cedar text cannot encode them.
pub fn render_artifacts(manifest: &Manifest) -> Result<BTreeMap<String, String>, String> {
    let mut artifacts: BTreeMap<String, (&Value, String)> = BTreeMap::new();
    for case in &manifest.cases {
        if !valid_revision_name(&case.revision) {
            return Err(format!("{}: invalid revision name", case.name));
        }
        match artifacts.entry(case.revision.clone()) {
            std::collections::btree_map::Entry::Occupied(entry) => {
                if entry.get().0 != case.policies.deref() {
                    return Err(format!("{}: conflicting revision output", case.revision));
                }
            }
            std::collections::btree_map::Entry::Vacant(entry) => {
                let policies = load_policy_set(&case.policies)?;
                let artifact = render_loaded_policy_set(&policies)
                    .map_err(|error| format!("{}: {error}", case.name))?;
                entry.insert((case.policies.deref(), artifact));
            }
        }
    }
    Ok(artifacts
        .into_iter()
        .map(|(revision, (_, artifact))| (revision, artifact))
        .collect())
}

struct ObservedDecision {
    decision: String,
    reasons: Vec<String>,
    error_policy_ids: Vec<String>,
}

fn check_case(
    case: &Case,
    policies: &PolicySet,
    rendered: &PolicySet,
    compiled_bodies: &BTreeMap<String, String>,
    rendered_bodies: &BTreeMap<String, String>,
    schema: Option<&Schema>,
    mut metrics: Option<&mut ReplayMetrics>,
) -> Result<ObservedDecision, String> {
    let started = metrics.as_ref().map(|_| Instant::now());
    let expected_ids = case.policy_ids.iter().cloned().collect::<BTreeSet<_>>();
    let loaded_ids = policies
        .policies()
        .map(|policy| policy.id().to_string())
        .collect::<BTreeSet<_>>();
    if expected_ids.len() != case.policy_ids.len() || expected_ids != loaded_ids {
        return Err("loaded policy IDs differ from the Lean compilation".into());
    }
    let entities = Entities::from_json_value(case.entities.clone(), schema)
        .map_err(|error| format!("Cedar schema entities: {error}"))?;
    let uid = |text: &str| EntityUid::from_str(text).map_err(|error| error.to_string());
    let action = uid(&case.request.action)?;
    let context = Context::from_json_value(
        case.request.context.clone(),
        schema.map(|checked| (checked, &action)),
    )
    .map_err(|error| format!("Cedar schema context: {error}"))?;
    let request = Request::new(
        uid(&case.request.principal)?,
        action,
        uid(&case.request.resource)?,
        context,
        schema,
    )
    .map_err(|error| format!("Cedar schema request: {error}"))?;
    if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
        stats.runtime_preparation_ns += started.elapsed().as_nanos();
    }
    let started = metrics.as_ref().map(|_| Instant::now());
    let response = Authorizer::new().is_authorized(&request, policies, &entities);
    if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), started) {
        stats.authorization_ns += started.elapsed().as_nanos();
        stats.authorization_calls += 1;
    }
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
    let started = metrics.as_ref().map(|_| Instant::now());
    let reparsed = Authorizer::new().is_authorized(&request, rendered, &entities);
    if let (Some(stats), Some(started)) = (metrics, started) {
        stats.authorization_ns += started.elapsed().as_nanos();
        stats.authorization_calls += 1;
    }
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
    Ok(ObservedDecision {
        decision: decision.into(),
        reasons: reasons.into_iter().collect(),
        error_policy_ids: error_policies.into_iter().collect(),
    })
}

#[cfg(test)]
#[path = "../tests/unit/bridge.rs"]
mod tests;
