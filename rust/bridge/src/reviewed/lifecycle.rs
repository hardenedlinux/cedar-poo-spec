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

fn provider_recovery(
    data: &Prepared,
    index: usize,
    seed: &Simulator,
    prepared: &PreparedPublications,
) -> Result<Vec<Value>, String> {
    if seed.prepare(&seed.envelope()).is_err() {
        return Ok(Vec::new());
    }
    let pending = seed.fork_simulation()?;
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let envelope = pending.envelope();
    let (_, lost) = pending.execute(
        pending.prepare(&envelope)?,
        &envelope,
        EffectIo {
            witness: &mut witness,
            provider: &mut provider,
            crash_after_send: true,
        },
    )?;
    if lost.is_some() {
        return Err("lost Gateway outcome unexpectedly returned".into());
    }
    let outcomes: Vec<_> = provider.signed_outcomes().cloned().collect();
    if outcomes.len() != 1 {
        return Err("provider did not retain its signed outcome".into());
    }
    let mut audit = pending.audit_authority(&witness);
    audit.prepared_publications = Some(prepared.clone());
    if cedar_poo_runtime::gateway::reconcile_provider_outcomes(
        &provider,
        &outcomes,
        &witness.snapshot(),
        cedar_poo_runtime::gateway::ProviderAuditTrust {
            authority: &audit,
            provider_key: &pending.provider_verifying_key(),
        },
    ) != Default::default()
    {
        return Err("independent provider audit failed".into());
    }
    let history = pending.publication_history()?;
    let settle = |authority: &Simulator,
                  journal: &ProviderJournal,
                  proofs: &[cedar_poo_runtime::gateway::Signed]| {
        Simulator::recover_with_provider_outcomes(
            authority,
            RecoveryEvidence {
                witness: &witness,
                publications: &history,
                audit: &audit,
                receipts: &[],
                provider: journal,
            },
            proofs,
        )
    };
    let mut rows = Vec::new();
    let missing = settle(&pending.fork_simulation()?, &provider, &[])?;
    rows.push(observe("provider-missing", &missing, prepared)?);
    let mut invalid = outcomes.clone();
    invalid[0].signature[0] ^= 1;
    let refused = settle(&pending.fork_simulation()?, &provider, &invalid)?;
    rows.push(observe("provider-invalid", &refused, prepared)?);
    let unobserved = settle(
        &pending.fork_simulation()?,
        &ProviderJournal::default(),
        &outcomes,
    )?;
    rows.push(observe("provider-unobserved", &unobserved, prepared)?);
    let mut evolved = Vec::new();
    for phase in ["expired", "renewed", "quarantined", "repaired", "world"] {
        let live = pending.fork_simulation()?;
        live.advance_time(100)?;
        match phase {
            "renewed" => live.refresh_facts(&data.restored.cases[index], 200)?,
            "quarantined" | "repaired" => {
                if live.refresh_facts(&data.restored.cases[index], 100).is_ok() {
                    return Err("expired source renewal succeeded".into());
                }
                if phase == "repaired" {
                    live.refresh_facts(&data.restored.cases[index], 200)?;
                }
            }
            "world" => live.refresh_facts(&data.empty_current.cases[index], 200)?,
            _ => (),
        }
        let before = live.lifecycle_view()?;
        let mut current_audit = live.audit_authority(&witness);
        current_audit.prepared_publications = Some(prepared.clone());
        let recovered = Simulator::recover_with_provider_outcomes(
            &live,
            RecoveryEvidence {
                witness: &witness,
                publications: &history,
                audit: &current_audit,
                receipts: &[],
                provider: &provider,
            },
            &outcomes,
        )?;
        let after = recovered.lifecycle_view()?;
        if after.unknown
            || !after.spent
            || after.fact_generation != before.fact_generation
            || after.sources_current != before.sources_current
            || after.now != before.now
            || after.world != before.world
            || after.revoked != before.revoked
        {
            return Err(format!(
                "provider settlement rewrote the live source image: {phase}"
            ));
        }
        evolved.push(observe(
            &format!("provider-{phase}-current-audit"),
            &recovered,
            prepared,
        )?);
    }
    let controlled = pending.fork_simulation()?;
    controlled.advance_time(100)?;
    controlled.revoke()?;
    controlled.replace_resource("replacement-incarnation".into(), 8)?;
    let replacement = controlled.envelope().effect;
    let complete = settle(&pending, &provider, &outcomes)?;
    rows.push(observe("provider-complete", &complete, prepared)?);
    if pending.prepare(&envelope).is_ok() {
        return Err("old provider-recovery owner admitted".into());
    }
    let repeated = settle(&complete, &provider, &outcomes)?;
    rows.push(observe("provider-repeated", &repeated, prepared)?);
    let controls = settle(&controlled, &provider, &outcomes)?;
    rows.push(observe("provider-current-controls", &controls, prepared)?);
    if controls.envelope().effect != replacement {
        return Err("provider settlement rolled back the current resource image".into());
    }
    rows.extend(evolved);
    if provider.actions.len() != 1 || provider.signed_outcomes().count() != 1 {
        return Err("provider recovery resent the effect".into());
    }
    Ok(rows)
}

fn scoped_recovery(
    data: &Prepared,
    index: usize,
    seed: &Simulator,
    prepared: &PreparedPublications,
) -> Result<Vec<Value>, String> {
    if seed.prepare(&seed.envelope()).is_err() {
        return Ok(Vec::new());
    }
    let mut foreign_case = data.restored.cases[index].clone();
    foreign_case.name.push_str("::independent-operation");
    let foreign_seed = Simulator::new(&foreign_case, Some(&data.restored.schema))?;
    foreign_seed.advance_time(11)?;
    foreign_seed.refresh_facts(&foreign_case, 200)?;
    let mut rows = Vec::new();
    for phase in [
        "foreign-pending-prefix",
        "foreign-complete-prefix",
        "foreign-complete-tail",
        "same-operation-duplicate",
        "unanchored-foreign",
        "invalid-foreign-signature",
    ] {
        let own = seed.fork_simulation()?;
        let foreign = if phase == "same-operation-duplicate" {
            seed.fork_simulation()?
        } else {
            foreign_seed.fork_simulation()?
        };
        let mut witness = Witness::simulation();
        let mut detached = Witness::simulation();
        let mut provider = ProviderJournal::default();
        let mut unavailable: ProviderJournal =
            serde_json::from_value(json!({"actions":[]})).map_err(|e| e.to_string())?;
        let foreign_envelope = foreign.envelope();
        if matches!(phase, "foreign-pending-prefix" | "foreign-complete-prefix") {
            foreign.execute(
                foreign.prepare(&foreign_envelope)?,
                &foreign_envelope,
                EffectIo {
                    witness: &mut witness,
                    provider: if phase == "foreign-pending-prefix" {
                        &mut unavailable
                    } else {
                        &mut provider
                    },
                    crash_after_send: true,
                },
            )?;
        }
        let envelope = own.envelope();
        own.execute(
            own.prepare(&envelope)?,
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: true,
            },
        )?;
        let own_prefix = (phase == "foreign-complete-tail").then(|| witness.snapshot());
        if !matches!(phase, "foreign-pending-prefix" | "foreign-complete-prefix") {
            foreign.execute(
                foreign.prepare(&foreign_envelope)?,
                &foreign_envelope,
                EffectIo {
                    witness: if phase == "unanchored-foreign" {
                        &mut detached
                    } else {
                        &mut witness
                    },
                    provider: &mut provider,
                    crash_after_send: true,
                },
            )?;
        }
        // Clone and inject the bounded fault in one traversal of the detached
        // evidence; do not perform a second membership scan inside the case loop.
        let mut corrupted = 0;
        let outcomes = provider
            .signed_outcomes()
            .map(|proof| {
                let mut proof = proof.clone();
                if phase == "invalid-foreign-signature" {
                    let outcome: cedar_poo_runtime::gateway::ProviderOutcome =
                        serde_json::from_slice(&proof.payload).map_err(|e| e.to_string())?;
                    if outcome.outcome.action.effect.operation == foreign_envelope.effect.operation
                    {
                        proof.signature[0] ^= 1;
                        corrupted += 1;
                    }
                }
                Ok(proof)
            })
            .collect::<Result<Vec<_>, String>>()?;
        if phase == "invalid-foreign-signature" && corrupted != 1 {
            return Err("foreign fault injection did not select exactly one proof".into());
        }
        let history = own.publication_history()?;
        let mut audit = own.audit_authority(&witness);
        audit.prepared_publications = Some(prepared.clone());
        if cedar_poo_runtime::gateway::reconcile_provider_outcomes(
            &provider,
            &outcomes,
            &witness.snapshot(),
            cedar_poo_runtime::gateway::ProviderAuditTrust {
                authority: &audit,
                provider_key: &own.provider_verifying_key(),
            },
        ) == Default::default()
        {
            return Err(format!("global audit hid the other operation: {phase}"));
        }
        own.revoke()?;
        own.advance_time(100)?;
        if own.refresh_facts(&data.restored.cases[index], 100).is_ok() {
            return Err("invalid scoped source renewal succeeded".into());
        }
        let before = own.lifecycle_view()?;
        let mut current_audit = own.audit_authority(&witness);
        current_audit.prepared_publications = Some(prepared.clone());
        let restored = Simulator::recover_with_provider_outcomes(
            &own,
            RecoveryEvidence {
                witness: &witness,
                publications: &history,
                audit: &current_audit,
                receipts: &[],
                provider: &provider,
            },
            &outcomes,
        )?;
        if phase == "foreign-complete-tail" {
            let prefix = own_prefix.as_ref().ok_or("missing own prefix control")?;
            let old_witness = Witness::restore(prefix, prefix.entries.len() as u64)?;
            let old_audit = restored.audit_authority(&old_witness);
            let rollback = Simulator::recover_with_provider_outcomes(
                &restored,
                RecoveryEvidence {
                    witness: &old_witness,
                    publications: &history,
                    audit: &old_audit,
                    receipts: &[],
                    provider: &provider,
                },
                &outcomes,
            );
            if !matches!(rollback, Err(error) if error.contains("witness frontier")) {
                return Err("recovery forgot the already authenticated shared tail".into());
            }
        }
        let after = restored.lifecycle_view()?;
        let unresolved = matches!(
            phase,
            "same-operation-duplicate" | "unanchored-foreign" | "invalid-foreign-signature"
        );
        if after.unknown != unresolved
            || !after.spent
            || !after.revoked
            || after.sources_current
            || after.now != before.now
            || after.fact_generation != before.fact_generation
            || restored.envelope().effect != envelope.effect
            || own.advance_time(101).is_ok()
        {
            return Err(format!(
                "scoped recovery lost current authorization controls: {phase}"
            ));
        }
        let expected_actions =
            if matches!(phase, "foreign-pending-prefix" | "same-operation-duplicate") {
                1
            } else {
                2
            };
        if provider.actions.len() != expected_actions
            || provider.signed_outcomes().count() != expected_actions
        {
            return Err("scoped recovery resent a provider effect".into());
        }
        rows.push(observe(&format!("scope-{phase}"), &restored, prepared)?);
    }
    Ok(rows)
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
    rows.extend(provider_recovery(data, index, &seed, &prepared)?);
    rows.extend(scoped_recovery(data, index, &seed, &prepared)?);
    let actual = json!({"states":rows,"publication":publication});
    if actual != group.plan.lifecycle[index] {
        return Err(format!(
            "continuous-use differs from actual Lean Contract: {}/{}; actual={}",
            group.entry, case.name, actual
        ));
    }
    Ok(json!({"entry":group.entry,"case":case.name,"lifecycle":actual}))
}
