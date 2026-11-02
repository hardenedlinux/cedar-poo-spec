//! SDK policy parsing, rendering and body/source conformance.
use crate::input::{Manifest, valid_revision_name};
use crate::{CompiledPolicyJson, TemplateSourceJson};
use cedar_policy::PolicySet;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::ops::Deref;

pub(crate) fn policy_bodies_by_id(
    policies: &PolicySet,
) -> Result<BTreeMap<String, String>, String> {
    policies
        .policies()
        .map(|policy| Ok((policy.id().to_string(), canonical_policy_body(policy)?)))
        .collect()
}

pub(crate) fn policy_body_counts(bodies: &BTreeMap<String, String>) -> BTreeMap<&str, usize> {
    let mut counts = BTreeMap::new();
    for body in bodies.values() {
        *counts.entry(body.as_str()).or_insert(0) += 1;
    }
    counts
}

pub(crate) fn canonical_policy_body(policy: &cedar_policy::Policy) -> Result<String, String> {
    // Stay in Cedar's public typed syntax representation. The prior path
    // serialized the parsed EST into Value and decoded it again solely to
    // obtain the normalized AST printer. Preserve independent text parsing.
    let syntax = policy
        .to_pst()
        .map_err(|error| format!("Cedar policy JSON: {error}"))?;
    let materialized = match syntax {
        cedar_policy::pst::Policy::Static(policy) => policy,
        cedar_policy::pst::Policy::Linked(policy) => policy
            .into_static_policy()
            .map_err(|error| format!("Cedar policy normalization: {error}"))?,
    };
    let normalized = cedar_policy::Policy::from_pst(materialized.into())
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
pub(crate) fn rendered_policy_bodies(
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

#[cfg(test)]
#[path = "../tests/unit/policy_codec.rs"]
mod tests;
