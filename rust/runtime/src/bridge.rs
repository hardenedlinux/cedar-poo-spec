//! Policy parsing, source verification and individual Cedar case execution.
use crate::entities::EntitySlot;
use crate::observation::{ReplayMetrics, revision_phase};
use std::fmt::Write;

pub(crate) use crate::canonical::json_sha256;
use crate::canonical::value_sha256;
use crate::{CompiledPolicyJson, TemplateSourceJson};
use cedar_policy::{
    AuthorizationError, Authorizer, Context, Decision, EntityUid, PolicySet, Request,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;
use std::path::Path;
use std::str::FromStr;
use std::time::Instant;

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

pub(crate) fn valid_revision_name(revision: &str) -> bool {
    revision.split('.').all(|segment| {
        !segment.is_empty()
            && segment
                .chars()
                .all(|character| character.is_ascii_alphanumeric() || character == '-')
    })
}

pub(crate) struct CheckedRevision {
    pub(crate) source: Value,
    pub(crate) policy_sha256: Option<String>,
    pub(crate) policies: PolicySet,
    pub(crate) rendered: PolicySet,
    pub(crate) compiled_bodies: BTreeMap<String, String>,
    pub(crate) rendered_bodies: BTreeMap<String, String>,
}

/// Only the text parser constructs this owner. Consequently every policy has
/// its complete original text; no lossy JSON/PST display is used as identity.
struct ParsedTextPolicies {
    policies: PolicySet,
}

impl ParsedTextPolicies {
    fn parse(text: &str) -> Result<Self, String> {
        PolicySet::from_str(text)
            .map(|policies| Self { policies })
            .map_err(|error| format!("rendered Cedar text parse: {error}"))
    }
}

/// One manifest invocation owns pure normalization results, keyed by complete
/// parsed source. SDK 4.12's text-to-JSON conversion reparses that exact text.
/// Hits avoid this repeated EST parse as well as JSON-to-AST normalization.
/// Revision names, policy IDs and observed decisions authorize no hit.
#[derive(Default)]
pub(crate) struct PreparedPolicyBodies {
    bodies: BTreeMap<String, String>,
}

impl PreparedPolicyBodies {
    fn bodies_by_id(
        &mut self,
        parsed: &ParsedTextPolicies,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<BTreeMap<String, String>, String> {
        let mut result = BTreeMap::new();
        for policy in parsed.policies.policies() {
            let key = policy
                .to_cedar()
                .ok_or("parsed static policy has no original Cedar text")?;
            let body = if let Some(body) = self.bodies.get(&key) {
                if let Some(stats) = metrics.as_deref_mut() {
                    stats.policy_body_reuses += 1;
                }
                body.clone()
            } else {
                // The original independent normalizer remains the miss path.
                let body = canonical_policy_body(policy)?;
                self.bodies.insert(key, body.clone());
                if let Some(stats) = metrics.as_deref_mut() {
                    stats.policy_body_normalizations += 1;
                    stats.policy_body_slot_peak =
                        stats.policy_body_slot_peak.max(self.bodies.len());
                }
                body
            };
            // Keep each actual parsed ID and all body multiplicities.
            result.insert(policy.id().to_string(), body);
        }
        Ok(result)
    }
}

/// A sealed source/parse pair. Validation can borrow it but cannot replace its body.
pub(crate) struct SourcePolicies {
    revision: String,
    source: Value,
    policies: PolicySet,
}
impl SourcePolicies {
    pub(crate) fn new(case: &Case) -> Result<Self, String> {
        Ok(Self {
            revision: case.revision.clone(),
            source: case.policies.deref().clone(),
            policies: load_policy_set(&case.policies)?,
        })
    }
    pub(crate) fn policies(&self) -> &PolicySet {
        &self.policies
    }
    pub(crate) fn checked(
        self,
        case: &Case,
        hash_for_receipt: bool,
        metrics: Option<&mut ReplayMetrics>,
        bodies: Option<&mut PreparedPolicyBodies>,
    ) -> Result<CheckedRevision, String> {
        if self.revision != case.revision || self.source != *case.policies.deref() {
            return Err("prepared policy source mismatch".into());
        }
        CheckedRevision::from_source(self, hash_for_receipt, metrics, bodies)
    }
}
impl CheckedRevision {
    pub(crate) fn new(
        case: &Case,
        hash_for_receipt: bool,
        mut metrics: Option<&mut ReplayMetrics>,
        bodies: Option<&mut PreparedPolicyBodies>,
    ) -> Result<Self, String> {
        let source = revision_phase(
            metrics.as_deref_mut(),
            |s| &mut s.revision_source_load_ns,
            || SourcePolicies::new(case),
        )?;
        source.checked(case, hash_for_receipt, metrics, bodies)
    }
    fn from_source(
        source: SourcePolicies,
        hash_for_receipt: bool,
        mut metrics: Option<&mut ReplayMetrics>,
        mut bodies: Option<&mut PreparedPolicyBodies>,
    ) -> Result<Self, String> {
        let SourcePolicies {
            source, policies, ..
        } = source;
        // SourcePolicies is sealed and loaded exclusively through Policy::from_json.
        // to_cedar already renders its normalized AST; retain those exact bodies.
        let (text, compiled_bodies) = revision_phase(
            metrics.as_deref_mut(),
            |s| &mut s.revision_render_ns,
            || rendered_policy_bodies(&policies),
        )?;
        let rendered = revision_phase(
            metrics.as_deref_mut(),
            |s| &mut s.revision_text_parse_ns,
            || ParsedTextPolicies::parse(&text),
        )?;
        // Every revision still parses its text independently. Identical complete
        // parsed text can share pure normalization within this invocation;
        // both authorizers and each revision's body comparison remain mandatory.
        let normalize_started = metrics.as_ref().map(|_| Instant::now());
        let rendered_bodies = if let Some(prepared) = bodies.as_mut() {
            prepared.bodies_by_id(&rendered, metrics.as_deref_mut())
        } else {
            policy_bodies_by_id(&rendered.policies)
        };
        if let (Some(stats), Some(started)) = (metrics.as_deref_mut(), normalize_started) {
            stats.revision_normalize_ns += started.elapsed().as_nanos();
        }
        let rendered_bodies = rendered_bodies?;
        let same = revision_phase(
            metrics.as_deref_mut(),
            |s| &mut s.revision_compare_ns,
            || policy_body_counts(&compiled_bodies) == policy_body_counts(&rendered_bodies),
        );
        if !same {
            return Err("rendered Cedar text changed policy bodies".into());
        }
        let policy_sha256 = revision_phase(
            metrics,
            |s| &mut s.revision_hash_ns,
            || {
                if hash_for_receipt {
                    value_sha256(&source).map(Some)
                } else {
                    Ok(None)
                }
            },
        )?;
        Ok(Self {
            source,
            policy_sha256,
            policies,
            rendered: rendered.policies,
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

fn policy_bodies_by_id(policies: &PolicySet) -> Result<BTreeMap<String, String>, String> {
    policies
        .policies()
        .map(|policy| Ok((policy.id().to_string(), canonical_policy_body(policy)?)))
        .collect()
}

fn policy_body_counts(bodies: &BTreeMap<String, String>) -> BTreeMap<&str, usize> {
    let mut counts = BTreeMap::new();
    for body in bodies.values() {
        *counts.entry(body.as_str()).or_insert(0) += 1;
    }
    counts
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
    rendered_policy_bodies(policies).map(|(text, _)| text)
}

// Keep sorted source bodies while rendering; no transient section strings/join buffer.
// For arbitrary text policies these are source bodies, not normalized bodies.
fn rendered_policy_bodies(
    policies: &PolicySet,
) -> Result<(String, BTreeMap<String, String>), String> {
    if policies.templates().next().is_some() {
        return Err("template source cannot render as a materialized policy file".into());
    }
    let bodies = policies
        .policies()
        .map(|policy| {
            let body = policy
                .to_cedar()
                .ok_or_else(|| "linked policy cannot render as Cedar text".to_owned())?;
            Ok((policy.id().to_string(), body))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let mut text =
        String::from("// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.\n");
    for (index, (id, body)) in bodies.iter().enumerate() {
        if index != 0 {
            text.push_str("\n\n");
        }
        // Writing to a String is infallible.
        write!(&mut text, "// POO policy ID: {id}\n{body}").expect("String formatting");
    }
    text.push('\n');
    Ok((text, bodies))
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
