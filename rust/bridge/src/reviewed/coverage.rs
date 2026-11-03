//! Every canonical Case is consumed exactly once by a qualified stage or refusal.
use super::{Bundle, Case, source_hash};
use crate::catalog_input::{Document, fields, is_schema_bound};
use std::collections::BTreeMap;

type Key = (String, String, String);
fn key(entry: &str, case: &Case) -> Key {
    (entry.into(), case.name.clone(), case.revision.clone())
}
fn identity(case: &Case) -> Result<String, String> {
    source_hash(&(
        &case.name,
        &case.revision,
        &case.policy_ids,
        &*case.policies,
        &*case.entities,
        &case.request,
        &case.expected,
        &case.expected_reasons,
        &case.expected_error_policies,
    ))
}
fn cases(document: &Document<'_>, raw: &str) -> Result<Vec<Case>, String> {
    if is_schema_bound(&fields(raw)) {
        Ok(document.sources.validated_manifest(raw)?.cases)
    } else {
        Ok(document.sources.manifest(raw)?.cases)
    }
}
fn inventory(document: &Document<'_>, name: &str) -> Result<BTreeMap<Key, String>, String> {
    let raw = *document
        .entries
        .get(name)
        .ok_or("missing canonical entry")?;
    let fields = fields(raw);
    let manifests = if fields.contains_key("cases") {
        vec![(name.to_owned(), cases(document, raw)?)]
    } else if name == "attested-schema-evolution" {
        let evolution = document.sources.evolution(raw)?;
        vec![
            (format!("{name}/before"), evolution.before.cases),
            (format!("{name}/after"), evolution.after.cases),
        ]
    } else {
        vec![]
    };
    let mut result = BTreeMap::new();
    for (label, rows) in manifests {
        for case in rows {
            if result
                .insert(key(&label, &case), identity(&case)?)
                .is_some()
            {
                return Err("duplicate canonical Case identity".into());
            }
        }
    }
    Ok(result)
}
pub(super) fn check(bundle: &Bundle, document: &Document<'_>, name: &str) -> Result<(), String> {
    if bundle.entry != name {
        return Err("reviewed fixture substituted its canonical entry".into());
    }
    let mut expected = inventory(document, name)?;
    for group in &bundle.groups {
        let stage = group.plan.stages.to_string();
        let staged = crate::catalog_input::document(&stage)?;
        let before = *staged
            .entries
            .get("before")
            .ok_or("missing original stage")?;
        for case in cases(&staged, before)? {
            if expected.remove(&key(&group.entry, &case)) != Some(identity(&case)?) {
                return Err("changed, duplicate or noncanonical original Case".into());
            }
        }
    }
    for refused in &bundle.refusals {
        for case in &refused.cases {
            if expected
                .remove(&(
                    refused.entry.clone(),
                    case.name.clone(),
                    case.revision.clone(),
                ))
                .is_none()
            {
                return Err("duplicate or noncanonical refused Case".into());
            }
        }
    }
    if !expected.is_empty() {
        return Err("canonical Cases omitted from reviewed coverage".into());
    }
    Ok(())
}
