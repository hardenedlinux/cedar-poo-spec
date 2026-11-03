//! Trusted Lean review fixtures to the shared native publication/effect owner.
use cedar_poo_core::{CompiledPolicyJson, SchemaSourceJson};
use cedar_poo_runtime::gateway::{
    AnalysisKind, EffectIo, Outcome, ProviderJournal, PublicationDelivery, ReleaseIdentity,
    ReviewAuthority, ReviewRecord, ReviewSubmission, Signed, Simulator, Version, Witness,
    reconcile,
};
use cedar_poo_runtime::{Case, ValidatedManifest, replay_validated_manifest};
use serde::Deserialize;
use serde_json::{Value, json};
use std::io::Write;
#[path = "coverage.rs"]
mod coverage;
#[path = "lifecycle.rs"]
mod lifecycle;
#[path = "runtime_benchmark.rs"]
mod runtime_benchmark;
pub(crate) use runtime_benchmark::benchmark;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Bundle {
    format_version: u64,
    entry: String,
    groups: Vec<Group>,
    refusals: Vec<RefusalSet>,
    original: Value,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RefusalSet {
    entry: String,
    cases: Vec<Refusal>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Refusal {
    name: String,
    revision: String,
    reason: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Group {
    entry: String,
    plan: Plan,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Plan {
    model: Value,
    schema: SchemaSourceJson,
    initial_root: String,
    stages: Value,
    reviews: Vec<Assessment>,
    expected_effects: Vec<Outcome>,
    lifecycle_stages: Value,
    lifecycle: Vec<Value>,
    tightening: Assessment,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Assessment {
    epoch: u64,
    before_root: String,
    after_root: String,
    before: CompiledPolicyJson,
    after: CompiledPolicyJson,
    analysis: AnalysisKind,
    environments_checked: u64,
    witnesses: Vec<WitnessPair>,
    without_approval: bool,
    with_approval: bool,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WitnessPair {
    before: Case,
    after: Case,
}
struct Prepared {
    before: ValidatedManifest,
    held: ValidatedManifest,
    restored: ValidatedManifest,
    reviews: Vec<Signed>,
    approvals: Vec<Signed>,
    release: ReleaseIdentity,
    empty_current: ValidatedManifest,
    empty_held: ValidatedManifest,
    tight_current: ValidatedManifest,
    tightening: Signed,
}
#[derive(Default)]
struct Totals {
    entries: usize,
    groups: usize,
    cases: usize,
    refusals: usize,
    publications: usize,
    gains: usize,
    continuous: bool,
}

fn source_hash(value: &impl serde::Serialize) -> Result<String, String> {
    // Domain identities use the same public SHA-256 receipt primitive.
    cedar_poo_runtime::gateway_source_sha256(value)
}
fn policy_hash(value: &CompiledPolicyJson) -> Result<String, String> {
    source_hash(&**value)
}

fn prepare(group: &Group, raw: &Value, issuer: &ReviewAuthority) -> Result<Prepared, String> {
    let plan = &group.plan;
    let stages = plan.stages.to_string();
    let document = crate::catalog_input::document(&stages)?;
    let at = |name: &str| {
        document
            .sources
            .validated_manifest(document.entries.get(name).ok_or("missing stage")?)
    };
    let before = at("before")?;
    let held = at("held")?;
    let restored = at("restored")?;
    if plan.reviews.len() != 2
        || before.cases.len() != held.cases.len()
        || held.cases.len() != restored.cases.len()
        || before.cases.len() != plan.expected_effects.len()
    {
        return Err("incomplete reviewed stages".into());
    }
    let release = ReleaseIdentity {
        root: plan.initial_root.clone(),
        source: source_hash(&plan.model)?,
    };
    let reviews = plan
        .reviews
        .iter()
        .enumerate()
        .map(|(index, report)| certify(report, &raw["plan"]["reviews"][index], plan, issuer))
        .collect::<Result<Vec<_>, String>>()?;
    let tightening = certify(&plan.tightening, &raw["plan"]["tightening"], plan, issuer)?;
    let lifecycle_document = plan.lifecycle_stages.to_string();
    let lifecycle = crate::catalog_input::document(&lifecycle_document)?;
    let at = |name: &str| {
        lifecycle.sources.validated_manifest(
            lifecycle
                .entries
                .get(name)
                .ok_or("missing lifecycle stage")?,
        )
    };
    let empty_current = at("current")?;
    let empty_held = at("held")?;
    let tight_current = at("tight")?;
    if empty_current.cases.len() != before.cases.len()
        || empty_held.cases.len() != before.cases.len()
        || tight_current.cases.len() != before.cases.len()
        || plan.lifecycle.len() != before.cases.len()
    {
        return Err("incomplete continuous-use stages".into());
    }
    let approvals = reviews
        .iter()
        .map(|review| issuer.approve(review))
        .collect::<Result<_, _>>()?;
    Ok(Prepared {
        before,
        held,
        restored,
        reviews,
        approvals,
        release,
        empty_current,
        empty_held,
        tight_current,
        tightening,
    })
}
fn certify(
    report: &Assessment,
    raw: &Value,
    plan: &Plan,
    issuer: &ReviewAuthority,
) -> Result<Signed, String> {
    validate_witnesses(report, &plan.schema)?;
    issuer.certify(&ReviewRecord {
        version: Version { major: 1, minor: 0 },
        before_root: report.before_root.clone(),
        after_root: report.after_root.clone(),
        before: policy_hash(&report.before)?,
        after: policy_hash(&report.after)?,
        schema: source_hash(&*plan.schema)?,
        source: source_hash(&plan.model)?,
        epoch: report.epoch,
        analysis: report.analysis.clone(),
        evidence: source_hash(raw)?,
    })
}
fn validate_witnesses(report: &Assessment, schema: &SchemaSourceJson) -> Result<(), String> {
    if report.environments_checked == 0
        || !report.with_approval
        || report.without_approval != (report.analysis == AnalysisKind::NoGain)
    {
        return Err("incoherent actual analyzer/Contract result".into());
    }
    if (report.analysis == AnalysisKind::NoGain) != report.witnesses.is_empty() {
        return Err("classification omitted or invented a gain witness".into());
    }
    for witness in &report.witnesses {
        let before = replay_validated_manifest(&ValidatedManifest {
            schema: schema.clone(),
            cases: vec![witness.before.clone()],
        })?
        .remove(0)
        .replay;
        let after = replay_validated_manifest(&ValidatedManifest {
            schema: schema.clone(),
            cases: vec![witness.after.clone()],
        })?
        .remove(0)
        .replay;
        if before.decision != "deny" || after.decision != "allow" {
            return Err("SDK refused the actual symbolic gain witness".into());
        }
    }
    Ok(())
}
fn check_view(
    sim: &Simulator,
    root: &str,
    policies: &CompiledPolicyJson,
    epoch: u64,
) -> Result<(), String> {
    let actual = sim.publication_view()?;
    if actual.root != root
        || actual.policies != policy_hash(policies)?
        || actual.epoch != epoch
        || actual.unknown
    {
        return Err("installed SDK release does not match the Lean successor".into());
    }
    Ok(())
}
fn run_case(prepared: &Prepared, index: usize, group: &Group) -> Result<Value, String> {
    let before = &prepared.before.cases[index];
    let held = &prepared.held.cases[index];
    let restored = &prepared.restored.cases[index];
    let sim = Simulator::with_release(before, &prepared.before.schema, prepared.release.clone())?;
    let old = sim.envelope();
    let old_handle = sim.prepare(&old).ok();
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let ticket = sim.register_review(ReviewSubmission {
        review: &prepared.reviews[0],
        candidate: held,
        approval: None,
    })?;
    if let Some(handle) = old_handle
        && sim
            .execute(
                handle,
                &old,
                EffectIo {
                    witness: &mut witness,
                    provider: &mut provider,
                    crash_after_send: false,
                },
            )
            .is_ok()
    {
        return Err("registration retained an old prepared effect".into());
    }
    sim.publish_review(ticket, PublicationDelivery::Complete)?;
    check_view(&sim, &group.plan.reviews[0].after_root, &held.policies, 8)?;
    if sim.prepare(&old).is_ok() || sim.prepare(&sim.envelope()).is_ok() {
        return Err("held release reused the old SDK Allow".into());
    }
    let unapproved = sim.register_review(ReviewSubmission {
        review: &prepared.reviews[1],
        candidate: restored,
        approval: None,
    });
    if unapproved.is_ok() != group.plan.reviews[1].without_approval {
        return Err("expansion bypassed the independent gain authority".into());
    }
    if sim
        .register_review(ReviewSubmission {
            review: &prepared.reviews[1],
            candidate: restored,
            approval: Some(&prepared.approvals[0]),
        })
        .is_ok()
    {
        return Err("approval for another review was reused".into());
    }
    let ticket = sim.register_review(ReviewSubmission {
        review: &prepared.reviews[1],
        candidate: restored,
        approval: Some(&prepared.approvals[1]),
    })?;
    sim.publish_review(ticket, PublicationDelivery::Complete)?;
    check_view(
        &sim,
        &group.plan.reviews[1].after_root,
        &restored.policies,
        9,
    )?;
    if sim
        .register_review(ReviewSubmission {
            review: &prepared.reviews[0],
            candidate: held,
            approval: None,
        })
        .is_ok()
    {
        return Err("retired review survived policy ABA".into());
    }
    let envelope = sim.envelope();
    let (outcome, receipt) = match sim.prepare(&envelope) {
        Ok(handle) => sim.execute(
            handle,
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: false,
            },
        )?,
        Err(_) => (
            Outcome {
                admitted: false,
                precommitted: false,
                sent: false,
                receipted: false,
                unknown: false,
            },
            None,
        ),
    };
    if outcome != group.plan.expected_effects[index] {
        return Err(format!("post-publication effect differs: {}", before.name));
    }
    let audit = reconcile(
        &provider,
        &receipt.into_iter().collect::<Vec<_>>(),
        &witness.snapshot(),
        &sim.audit_authority(&witness),
    );
    if audit != Default::default() {
        return Err("independent audit rejected the reviewed effect".into());
    }
    Ok(
        json!({"entry":group.entry,"case":before.name,"publication":sim.publication_view()?,"outcome":outcome,"audit":audit}),
    )
}
fn qualify_group(
    group: &Group,
    raw: &Value,
    totals: &mut Totals,
    output: &mut impl Write,
) -> Result<(), String> {
    let prepared = prepare(group, raw, &ReviewAuthority::simulation())?;
    for index in 0..prepared.before.cases.len() {
        let row = if totals.continuous {
            lifecycle::run_case(&prepared, index, group)?
        } else {
            run_case(&prepared, index, group)?
        };
        serde_json::to_writer(&mut *output, &row).map_err(|e| e.to_string())?;
        writeln!(output).map_err(|e| e.to_string())?;
        totals.cases += 1;
        totals.publications += if totals.continuous { 3 } else { 2 };
    }
    totals.groups += 1;
    totals.gains += group
        .plan
        .reviews
        .iter()
        .filter(|review| review.analysis != AnalysisKind::NoGain)
        .count();
    Ok(())
}
fn validate_refusals(bundle: &Bundle) -> Result<usize, String> {
    let original = bundle.original.to_string();
    let document = crate::catalog_input::document(&original)?;
    let base = *document
        .entries
        .get(&bundle.entry)
        .ok_or("missing original entry")?;
    let mut count = 0;
    for refused in &bundle.refusals {
        let raw = if refused.entry == bundle.entry {
            base
        } else {
            let fields = crate::catalog_input::fields(base);
            let side = refused
                .entry
                .strip_prefix(&(bundle.entry.clone() + "/"))
                .ok_or("unbound refusal entry")?;
            *fields.get(side).ok_or("unbound refusal side")?
        };
        let cases = if crate::catalog_input::is_schema_bound(&crate::catalog_input::fields(raw)) {
            document.sources.validated_manifest(raw)?.cases
        } else {
            document.sources.manifest(raw)?.cases
        };
        let cases: std::collections::BTreeMap<_, _> = cases
            .iter()
            .map(|case| ((case.name.as_str(), case.revision.as_str()), case))
            .collect();
        for refusal in &refused.cases {
            let case = cases
                .get(&(refusal.name.as_str(), refusal.revision.as_str()))
                .ok_or("unbound refused Case")?;
            if refusal.reason.is_empty() {
                return Err("missing qualification refusal".into());
            }
            let simulator = Simulator::new(case, None)?;
            if simulator.prepare(&simulator.envelope()).is_ok() {
                return Err("unqualified source acquired effect authority".into());
            }
            count += 1;
        }
    }
    Ok(count)
}
fn qualify_bundle(
    input: &str,
    canonical: &crate::catalog_input::Document<'_>,
    name: &str,
    totals: &mut Totals,
    output: &mut impl Write,
) -> Result<(), String> {
    let raw: Value = serde_json::from_str(input).map_err(|e| e.to_string())?;
    let bundle: Bundle = serde_json::from_str(input).map_err(|e| e.to_string())?;
    if bundle.format_version != 1 {
        return Err("unsupported reviewed fixture".into());
    }
    coverage::check(&bundle, canonical, name)?;
    for (index, group) in bundle.groups.iter().enumerate() {
        qualify_group(group, &raw["groups"][index], totals, output)?;
    }
    // Refusals are explicit inputs too, never silently promoted to enforcing profiles.
    totals.refusals += validate_refusals(&bundle)?;
    totals.entries += 1;
    eprintln!(
        "REVIEWED-ENTRY: {}; groups={}; cases={}",
        bundle.entry,
        bundle.groups.len(),
        totals.cases
    );
    Ok(())
}
pub(crate) fn replay(
    input: &str,
    directory: &str,
    output: &mut impl Write,
    continuous: bool,
) -> Result<(), String> {
    let original = crate::catalog::replay(input)?;
    let names = original.as_object().ok_or("missing canonical entries")?;
    let canonical = crate::catalog_input::document(input)?;
    let mut totals = Totals {
        continuous,
        ..Totals::default()
    };
    for name in names.keys() {
        if !name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
        {
            return Err("unsafe canonical entry name".into());
        }
        let path = std::path::Path::new(directory).join(format!("{name}.json"));
        qualify_bundle(
            &std::fs::read_to_string(path).map_err(|e| e.to_string())?,
            &canonical,
            name,
            &mut totals,
            output,
        )?;
    }
    if totals.entries != 51
        || totals.groups == 0
        || totals.gains == 0
        || totals.cases + totals.refusals != 1292
    {
        return Err("incomplete nonidentity domain coverage".into());
    }
    eprintln!(
        "REVIEWED-EFFECTS-OK: entries={}; groups={}; cases={}; refusals={}; publications={}; gains={}",
        totals.entries,
        totals.groups,
        totals.cases,
        totals.refusals,
        totals.publications,
        totals.gains
    );
    serde_json::to_writer(
        &mut *output,
        &json!({"kind":"summary","continuous":continuous,"lifecycle_outcomes":if continuous { totals.cases * 13 } else { 0 },"entries":totals.entries,
        "groups":totals.groups,"cases":totals.cases,"refusals":totals.refusals,
        "publications":totals.publications,"gains":totals.gains}),
    )
    .map_err(|e| e.to_string())?;
    writeln!(output).map_err(|e| e.to_string())?;
    output.flush().map_err(|e| e.to_string())
}

fn install_prepared(prepared: &Prepared, index: usize) -> Result<(Case, Simulator), String> {
    let before = &prepared.before.cases[index];
    let simulator =
        Simulator::with_release(before, &prepared.before.schema, prepared.release.clone())?;
    activate_prepared(&simulator, prepared, index)?;
    Ok((prepared.restored.cases[index].clone(), simulator))
}
fn activate_prepared(
    simulator: &Simulator,
    prepared: &Prepared,
    index: usize,
) -> Result<(), String> {
    let held = simulator.register_review(ReviewSubmission {
        review: &prepared.reviews[0],
        candidate: &prepared.held.cases[index],
        approval: None,
    })?;
    simulator.publish_review(held, PublicationDelivery::Complete)?;
    let restored = simulator.register_review(ReviewSubmission {
        review: &prepared.reviews[1],
        candidate: &prepared.restored.cases[index],
        approval: Some(&prepared.approvals[1]),
    })?;
    simulator.publish_review(restored, PublicationDelivery::Complete)?;
    Ok(())
}
/// Only startup configuration loads analyzer output and independent mock approvals.
pub(crate) fn stdio(path: &str, index: usize, enforce: bool) -> Result<(), String> {
    let input = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let raw: Value = serde_json::from_str(&input).map_err(|e| e.to_string())?;
    let bundle: Bundle = serde_json::from_str(&input).map_err(|e| e.to_string())?;
    if bundle.format_version != 1 {
        return Err("unsupported reviewed fixture".into());
    }
    let group = bundle
        .groups
        .get(index)
        .ok_or("reviewed profile group is absent")?;
    let prepared = prepare(group, &raw["groups"][index], &ReviewAuthority::simulation())?;
    let profiles = (0..prepared.before.cases.len())
        .map(|case| install_prepared(&prepared, case))
        .collect::<Result<Vec<_>, _>>()?;
    crate::gateway::serve(crate::gateway::McpSimulation::from_profiles(
        profiles, enforce,
    )?)
}

#[cfg(test)]
#[path = "../../tests/unit/reviewed.rs"]
mod tests;
