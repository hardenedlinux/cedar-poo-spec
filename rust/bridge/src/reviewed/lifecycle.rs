//! Continuous-use replay over the same actual C4 publications and trusted sources.
use super::{Group, Prepared, install_prepared};
use cedar_poo_runtime::gateway::{
    EffectIo, Outcome, PreparedPublications, ProviderJournal, PublicationDelivery,
    RecoveryEvidence, ReviewSubmission, Simulator, Witness, reconcile,
};
use serde_json::{Value, json};

fn outcome(sim: &Simulator, prepared: &PreparedPublications) -> Result<Outcome, String> {
    let probe = sim.fork_simulation()?;
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let envelope = probe.envelope();
    let (outcome, receipt) = if let Ok(handle) = probe.prepare(&envelope) {
        probe.execute(
            handle,
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: false,
            },
        )?
    } else {
        (
            Outcome {
                admitted: false,
                precommitted: false,
                sent: false,
                receipted: false,
                unknown: false,
            },
            None,
        )
    };
    let mut authority = probe.audit_authority(&witness);
    authority.prepared_publications = Some(prepared.clone());
    let report = reconcile(
        &provider,
        &receipt.into_iter().collect::<Vec<_>>(),
        &witness.snapshot(),
        &authority,
    );
    if report != Default::default() {
        return Err("independent current-use probe audit failed".into());
    }
    Ok(outcome)
}
fn observe(label: &str, sim: &Simulator, prepared: &PreparedPublications) -> Result<Value, String> {
    let view = sim.lifecycle_view()?;
    Ok(
        json!({"label":label,"outcome":outcome(sim, prepared)?,"spent":view.spent,"sources_current":view.sources_current,
        "unknown":view.unknown,"revoked":view.revoked,"fact_generation":view.fact_generation,
        "now":view.now,"epoch":view.policy_epoch}),
    )
}
fn refuse_old(sim: &Simulator, old: &cedar_poo_runtime::gateway::Envelope) -> Result<(), String> {
    if sim.prepare(old).is_ok() {
        return Err("old source evidence survived renewal".into());
    }
    Ok(())
}
fn worlds(
    data: &Prepared,
    index: usize,
    seed: &Simulator,
    prepared: &PreparedPublications,
) -> Result<(Vec<Value>, bool), String> {
    let sim = seed.fork_simulation()?;
    let mut rows = vec![observe("initial", &sim, prepared)?];
    let old = sim.envelope();
    let old_handle = sim.prepare(&old).ok();
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    sim.advance_time(100)?;
    rows.push(observe("expired", &sim, prepared)?);
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
        return Err("expired prepared handle dispatched".into());
    }
    let before = sim.lifecycle_view()?;
    if sim.advance_time(99).is_ok() || sim.lifecycle_view()? != before {
        return Err("source clock rolled back".into());
    }
    if sim
        .register_review(ReviewSubmission {
            review: &data.tightening,
            candidate: &data.tight_current.cases[index],
            approval: None,
        })
        .is_ok()
    {
        return Err("expired facts allowed publication registration".into());
    }
    sim.refresh_facts(&data.restored.cases[index], 200)?;
    refuse_old(&sim, &old)?;
    let renewed = sim.envelope();
    rows.push(observe("renewed", &sim, prepared)?);
    sim.refresh_facts(&data.empty_current.cases[index], 200)?;
    refuse_old(&sim, &renewed)?;
    rows.push(observe("entities", &sim, prepared)?);
    let changed_world = sim.lifecycle_view()?.world != old.current_world;
    let before_trial = sim.lifecycle_view()?;
    let trial = sim.register_review(ReviewSubmission {
        review: &data.tightening,
        candidate: &data.empty_held.cases[index],
        approval: None,
    });
    let publication = trial.is_ok();
    if changed_world {
        if trial.is_ok() || sim.lifecycle_view()? != before_trial {
            return Err("changed-world publication escaped its pinned release chain".into());
        }
    } else if trial.is_err() {
        return Err("same-world no-gain registration was unexpectedly refused".into());
    }
    sim.refresh_facts(&data.restored.cases[index], 200)?;
    refuse_old(&sim, &renewed)?;
    if let Ok(ticket) = trial
        && sim
            .publish_review(ticket, PublicationDelivery::Complete)
            .is_ok()
    {
        return Err("fact renewal retained an old publication ticket".into());
    }
    rows.push(observe("world-aba", &sim, prepared)?);
    let ticket = sim.register_review(ReviewSubmission {
        review: &data.tightening,
        candidate: &data.tight_current.cases[index],
        approval: None,
    })?;
    sim.publish_review(ticket, PublicationDelivery::Complete)?;
    rows.push(observe("policy", &sim, prepared)?);
    if !witness.entries().is_empty() || !provider.actions.is_empty() {
        return Err("refused control produced an effect".into());
    }
    Ok((rows, publication))
}
fn revoked(
    data: &Prepared,
    index: usize,
    seed: &Simulator,
    prepared: &PreparedPublications,
) -> Result<Vec<Value>, String> {
    let sim = seed.fork_simulation()?;
    sim.revoke()?;
    if sim
        .register_review(ReviewSubmission {
            review: &data.tightening,
            candidate: &data.tight_current.cases[index],
            approval: None,
        })
        .is_ok()
    {
        return Err("revoked operation registered a new publication".into());
    }
    let mut rows = vec![observe("revoked", &sim, prepared)?];
    let witness = Witness::simulation();
    let provider = ProviderJournal::default();
    let history = sim.publication_history()?;
    let mut audit = sim.audit_authority(&witness);
    audit.prepared_publications = Some(prepared.clone());
    let restored = Simulator::recover(
        &sim,
        RecoveryEvidence {
            publications: &history,
            audit: &audit,
            witness: &witness,
            receipts: &[],
            provider: &provider,
        },
    )?;
    rows.push(observe("recovered-revoked", &restored, prepared)?);
    if sim.advance_time(11).is_ok() || sim.prepare(&sim.envelope()).is_ok() {
        return Err("replaced mediator retained write/use authority".into());
    }
    if restored.lifecycle_view()?.fact_generation != 7
        || restored.lifecycle_view()?.policy_epoch != 9
    {
        return Err("recovery changed source or policy frontier".into());
    }
    Ok(rows)
}
fn burned(seed: &Simulator, crash: bool, prepared: &PreparedPublications) -> Result<Value, String> {
    let sim = seed.fork_simulation()?;
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let envelope = sim.envelope();
    let receipt = if let Ok(handle) = sim.prepare(&envelope) {
        sim.execute(
            handle,
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: crash,
            },
        )?
        .1
    } else {
        None
    };
    let receipts: Vec<_> = receipt.into_iter().collect();
    let mut audit = sim.audit_authority(&witness);
    audit.prepared_publications = Some(prepared.clone());
    if !crash && reconcile(&provider, &receipts, &witness.snapshot(), &audit) != Default::default()
    {
        return Err("independent current-world outcome audit failed".into());
    }
    let history = sim.publication_history()?;
    let restored = Simulator::recover(
        &sim,
        RecoveryEvidence {
            publications: &history,
            audit: &audit,
            witness: &witness,
            receipts: &receipts,
            provider: &provider,
        },
    )?;
    if sim.prepare(&envelope).is_ok() {
        return Err("retired owner admitted a fresh effect".into());
    }
    observe(
        if crash {
            "recovered-unknown"
        } else {
            "recovered-complete"
        },
        &restored,
        prepared,
    )
}
fn failed_source(
    data: &Prepared,
    index: usize,
    seed: &Simulator,
    prepared: &PreparedPublications,
) -> Result<Vec<Value>, String> {
    let sim = seed.fork_simulation()?;
    if sim.refresh_facts(&data.restored.cases[index], 10).is_ok() {
        return Err("invalid source lease refreshed authority".into());
    }
    let mut rows = vec![observe("failed-refresh", &sim, prepared)?];
    let witness = Witness::simulation();
    let provider = ProviderJournal::default();
    let history = sim.publication_history()?;
    let mut audit = sim.audit_authority(&witness);
    audit.prepared_publications = Some(prepared.clone());
    let restored = Simulator::recover(
        &sim,
        RecoveryEvidence {
            publications: &history,
            audit: &audit,
            witness: &witness,
            receipts: &[],
            provider: &provider,
        },
    )?;
    rows.push(observe("recovered-failed-refresh", &restored, prepared)?);
    restored.refresh_facts(&data.restored.cases[index], 200)?;
    rows.push(observe("repaired-refresh", &restored, prepared)?);
    Ok(rows)
}
fn recovery_boundaries(
    case: &cedar_poo_runtime::Case,
    seed: &Simulator,
    prepared: &PreparedPublications,
) -> Result<Vec<Value>, String> {
    if seed.prepare(&seed.envelope()).is_err() {
        return Ok(Vec::new());
    }
    let uncertain = seed.fork_simulation()?;
    uncertain.refresh_facts(case, 200)?;
    let mut original_log = Witness::simulation();
    let mut original_provider = ProviderJournal::default();
    let envelope = uncertain.envelope();
    uncertain.execute(
        uncertain.prepare(&envelope)?,
        &envelope,
        EffectIo {
            witness: &mut original_log,
            provider: &mut original_provider,
            crash_after_send: true,
        },
    )?;
    let alternate = seed.fork_simulation()?;
    let mut alternate_log = Witness::simulation();
    let mut alternate_provider = ProviderJournal::default();
    let envelope = alternate.envelope();
    let (_, receipt) = alternate.execute(
        alternate.prepare(&envelope)?,
        &envelope,
        EffectIo {
            witness: &mut alternate_log,
            provider: &mut alternate_provider,
            crash_after_send: false,
        },
    )?;
    let receipts = vec![receipt.ok_or("missing alternate outcome")?];
    let mut audit = alternate.audit_authority(&alternate_log);
    audit.prepared_publications = Some(prepared.clone());
    if reconcile(
        &alternate_provider,
        &receipts,
        &alternate_log.snapshot(),
        &audit,
    ) != Default::default()
    {
        return Err("alternate observation was not independently clean".into());
    }
    let history = uncertain.publication_history()?;
    let before = uncertain.lifecycle_view()?;
    if Simulator::recover(
        &uncertain,
        RecoveryEvidence {
            witness: &alternate_log,
            publications: &history,
            audit: &audit,
            receipts: &receipts,
            provider: &alternate_provider,
        },
    )
    .is_ok()
        || uncertain.lifecycle_view()? != before
    {
        return Err("clean alternate history replaced the retained intent".into());
    }
    let empty = Witness::simulation();
    let empty_provider = ProviderJournal::default();
    let empty_audit = uncertain.audit_authority(&empty);
    if Simulator::recover(
        &uncertain,
        RecoveryEvidence {
            witness: &empty,
            publications: &history,
            audit: &empty_audit,
            receipts: &[],
            provider: &empty_provider,
        },
    )
    .is_ok()
        || uncertain.lifecycle_view()? != before
    {
        return Err("truncated history replaced the retained intent".into());
    }
    let unbound = seed.fork_simulation()?;
    let before_unbound = unbound.lifecycle_view()?;
    if Simulator::recover(
        &unbound,
        RecoveryEvidence {
            witness: &alternate_log,
            publications: &history,
            audit: &audit,
            receipts: &receipts,
            provider: &alternate_provider,
        },
    )
    .is_ok()
        || unbound.lifecycle_view()? != before_unbound
    {
        return Err("external history manufactured a local intent".into());
    }
    Ok(vec![
        observe("substituted-recovery", &uncertain, prepared)?,
        observe("truncated-recovery", &uncertain, prepared)?,
        observe("unbound-recovery", &unbound, prepared)?,
    ])
}

pub(super) fn run_case(data: &Prepared, index: usize, group: &Group) -> Result<Value, String> {
    let (case, seed) = install_prepared(data, index)?;
    let prepared = PreparedPublications::new(
        &seed.publication_history()?,
        &seed.verifying_key(),
        &seed.review_trust(),
    )?;
    let (mut rows, publication) = worlds(data, index, &seed, &prepared)?;
    rows.extend(revoked(data, index, &seed, &prepared)?);
    rows.push(burned(&seed, false, &prepared)?);
    rows.push(burned(&seed, true, &prepared)?);
    rows.extend(failed_source(data, index, &seed, &prepared)?);
    rows.extend(recovery_boundaries(&case, &seed, &prepared)?);
    let actual = json!({"states":rows,"publication":publication});
    if actual != group.plan.lifecycle[index] {
        return Err(format!(
            "continuous-use differs from actual Lean Contract: {}/{}; actual={}",
            group.entry, case.name, actual
        ));
    }
    Ok(json!({"entry":group.entry,"case":case.name,"lifecycle":actual}))
}
