use super::{Bundle, Group, Prepared, install_prepared, prepare, source_hash};
use cedar_poo_runtime::gateway::{
    AnalysisKind, EffectIo, Fault, ProviderJournal, PublicationDelivery, RecoveryEvidence,
    ReviewAuthority, ReviewRecord, ReviewSubmission, ReviewedRecovery, Signed, Simulator, Witness,
    verify_publications,
};
use serde_json::Value;

fn fixture() -> (Group, Prepared, usize) {
    let file = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/reviewed-effects/agent-payment-validated.json");
    let input = std::fs::read_to_string(file).expect("run just check-reviewed-effects");
    let raw: Value = serde_json::from_str(&input).unwrap();
    let bundle: Bundle = serde_json::from_str(&input).unwrap();
    for (offset, group) in bundle.groups.into_iter().enumerate() {
        let prepared = prepare(
            &group,
            &raw["groups"][offset],
            &ReviewAuthority::simulation(),
        )
        .unwrap();
        if let Some(index) =
            prepared.before.cases.iter().position(|case| {
                case.expected == "allow" && case.expected_error_policies.is_empty()
            })
        {
            return (group, prepared, index);
        }
    }
    panic!("real fixture must contain an executable reviewed Case")
}
fn simulator(data: &Prepared, index: usize) -> Simulator {
    Simulator::with_release(
        &data.before.cases[index],
        &data.before.schema,
        data.release.clone(),
    )
    .unwrap()
}
fn submit<'a>(
    data: &'a Prepared,
    index: usize,
    leg: usize,
    approval: Option<&'a Signed>,
) -> ReviewSubmission<'a> {
    ReviewSubmission {
        review: &data.reviews[leg],
        candidate: if leg == 0 {
            &data.held.cases[index]
        } else {
            &data.restored.cases[index]
        },
        approval,
    }
}

#[test]
#[ignore = "requires actual Lean Delta output; run just check-reviewed-effects"]
fn review_authentication_and_every_source_binding_are_mandatory() {
    let (_, data, index) = fixture();
    let issuer = ReviewAuthority::simulation();
    let mut forged = data.reviews[0].clone();
    forged.signature[0] ^= 1;
    let sim = simulator(&data, index);
    assert!(
        sim.register_review(ReviewSubmission {
            review: &forged,
            candidate: &data.held.cases[index],
            approval: None
        })
        .is_err()
    );
    let original: ReviewRecord = sim.review_trust().verify_review(&data.reviews[0]).unwrap();
    let edits: [fn(&mut ReviewRecord); 6] = [
        |r| r.before_root.push_str("-stale"),
        |r| r.before.push('0'),
        |r| r.after.push('0'),
        |r| r.schema.push('0'),
        |r| r.source.push('0'),
        |r| r.epoch += 1,
    ];
    for edit in edits {
        let mut record = original.clone();
        edit(&mut record);
        let signed = issuer.certify(&record).unwrap();
        let sim = simulator(&data, index);
        let before = sim.publication_view().unwrap();
        assert!(
            sim.register_review(ReviewSubmission {
                review: &signed,
                candidate: &data.held.cases[index],
                approval: None
            })
            .is_err()
        );
        assert_eq!(sim.publication_view().unwrap(), before);
    }
    let (case, sim) = install_prepared(&data, index).unwrap();
    assert!(sim.prepare(&sim.envelope()).is_ok());
    assert_eq!(case.expected, "allow");
}
#[test]
#[ignore = "requires actual Lean Delta output; run just check-reviewed-effects"]
fn replaced_foreign_stale_and_non_enforcing_publications_refuse() {
    let (_, data, index) = fixture();
    let first = simulator(&data, index);
    let other = simulator(&data, index);
    let foreign = other
        .register_review(submit(&data, index, 0, None))
        .unwrap();
    assert!(
        first
            .publish_review(foreign, PublicationDelivery::Complete)
            .is_err()
    );
    let old = first
        .register_review(submit(&data, index, 0, None))
        .unwrap();
    let new = first
        .register_review(submit(&data, index, 0, None))
        .unwrap();
    assert!(
        first
            .publish_review(old, PublicationDelivery::Complete)
            .is_err()
    );
    first
        .publish_review(new, PublicationDelivery::Complete)
        .unwrap();
    assert!(
        first
            .register_review(submit(&data, index, 0, None))
            .is_err()
    );
    let paused = simulator(&data, index);
    let ticket = paused
        .register_review(submit(&data, index, 0, None))
        .unwrap();
    paused
        .mutate(Fault::Observing, &mut paused.envelope())
        .unwrap();
    assert!(
        paused
            .publish_review(ticket, PublicationDelivery::Complete)
            .is_err()
    );
    assert_eq!(paused.publication_view().unwrap().epoch, 7);
}
#[test]
#[ignore = "requires actual Lean Delta output; run just check-reviewed-effects"]
fn a_caller_no_gain_claim_and_an_approval_for_another_review_cannot_expand() {
    let (_, data, index) = fixture();
    let sim = simulator(&data, index);
    let held = sim.register_review(submit(&data, index, 0, None)).unwrap();
    sim.publish_review(held, PublicationDelivery::Complete)
        .unwrap();
    assert_ne!(
        sim.review_trust()
            .verify_review(&data.reviews[1])
            .unwrap()
            .analysis,
        AnalysisKind::NoGain
    );
    assert!(sim.register_review(submit(&data, index, 1, None)).is_err());
    assert!(
        sim.register_review(submit(&data, index, 1, Some(&data.approvals[0])))
            .is_err()
    );
    let mut false_report = sim.review_trust().verify_review(&data.reviews[1]).unwrap();
    false_report.analysis = AnalysisKind::NoGain;
    let forged = Signed {
        payload: serde_json::to_vec(&false_report).unwrap(),
        signature: data.reviews[1].signature.clone(),
    };
    assert!(
        sim.register_review(ReviewSubmission {
            review: &forged,
            candidate: &data.restored.cases[index],
            approval: None
        })
        .is_err()
    );
    assert_eq!(sim.publication_view().unwrap().epoch, 8);
}
#[test]
#[ignore = "requires actual Lean Delta output; run just check-reviewed-effects"]
fn publication_reply_loss_recovery_and_effect_loss_preserve_separate_exposures() {
    let (_, data, index) = fixture();
    let sim = simulator(&data, index);
    let ticket = sim.register_review(submit(&data, index, 0, None)).unwrap();
    let lost = sim
        .publish_review(ticket, PublicationDelivery::LostReply)
        .unwrap();
    assert!(lost.unknown && lost.epoch == 8);
    assert!(
        sim.register_review(submit(&data, index, 1, Some(&data.approvals[1])))
            .is_err()
    );
    assert!(sim.confirm_publication(&[]).is_err());
    sim.confirm_publication(&sim.publication_history().unwrap())
        .unwrap();
    let ticket = sim
        .register_review(submit(&data, index, 1, Some(&data.approvals[1])))
        .unwrap();
    sim.publish_review(ticket, PublicationDelivery::Complete)
        .unwrap();
    let history = sim.publication_history().unwrap();
    assert!(verify_publications(&history[1..], &sim.verifying_key(), &sim.review_trust()).is_err());
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let envelope = sim.envelope();
    let (outcome, receipt) = sim
        .execute(
            sim.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: true,
            },
        )
        .unwrap();
    assert!(outcome.unknown && receipt.is_none());
    sim.confirm_publication(&history).unwrap();
    assert!(sim.prepare(&sim.envelope()).is_err());
    let recovered = Simulator::recover_reviewed(
        &data.restored.cases[index],
        &data.before.schema,
        ReviewedRecovery {
            release: data.release.clone(),
            publications: &history,
            effects: RecoveryEvidence {
                witness: &witness,
                receipts: &[],
                provider: &provider,
            },
        },
    )
    .unwrap();
    assert_eq!(recovered.publication_view().unwrap().epoch, 9);
    assert!(recovered.prepare(&recovered.envelope()).is_err());
    assert!(
        recovered
            .register_review(submit(&data, index, 0, None))
            .is_err()
    );
    assert!(
        Simulator::recover(
            &data.restored.cases[index],
            Some(&data.before.schema),
            RecoveryEvidence {
                witness: &witness,
                receipts: &[],
                provider: &provider
            }
        )
        .is_err()
    );
    assert_eq!(provider.actions.len(), 1);
    assert!(!source_hash(&history).unwrap().is_empty());
}

#[test]
#[ignore = "requires actual Lean Delta output; run just check-reviewed-effects"]
fn fresh_reviewed_recovery_keeps_epoch_and_public_audit_requires_review_trust() {
    let (_, data, index) = fixture();
    let (_, sim) = install_prepared(&data, index).unwrap();
    let history = sim.publication_history().unwrap();
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let restored = Simulator::recover_reviewed(
        &data.restored.cases[index],
        &data.before.schema,
        ReviewedRecovery {
            release: data.release.clone(),
            publications: &history,
            effects: RecoveryEvidence {
                witness: &witness,
                receipts: &[],
                provider: &provider,
            },
        },
    )
    .unwrap();
    assert_eq!(restored.publication_view().unwrap().epoch, 9);
    let envelope = restored.envelope();
    let (outcome, receipt) = restored
        .execute(
            restored.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    assert!(outcome.receipted && !outcome.unknown);
    let receipts = [receipt.unwrap()];
    let snapshot = witness.snapshot();
    let mut trust = restored.audit_authority(&witness);
    assert_eq!(
        cedar_poo_runtime::gateway::reconcile(&provider, &receipts, &snapshot, &trust),
        Default::default()
    );
    trust.review_trust = None;
    let refused = cedar_poo_runtime::gateway::reconcile(&provider, &receipts, &snapshot, &trust);
    assert_eq!(refused.invalid_receipts, 1);
    assert_eq!(refused.unresolved_precommits.len(), 1);
    assert_eq!(refused.missing_receipts.len(), 1);
    let recovered = Simulator::recover_reviewed(
        &data.restored.cases[index],
        &data.before.schema,
        ReviewedRecovery {
            release: data.release.clone(),
            publications: &history,
            effects: RecoveryEvidence {
                witness: &witness,
                receipts: &receipts,
                provider: &provider,
            },
        },
    )
    .unwrap();
    assert_eq!(recovered.publication_view().unwrap().epoch, 9);
    assert!(recovered.prepare(&recovered.envelope()).is_err());
    assert_eq!(provider.actions.len(), 1);
    let mut tampered = history.clone();
    tampered[1].payload[0] ^= 1;
    assert!(
        verify_publications(
            &tampered,
            &restored.verifying_key(),
            &restored.review_trust()
        )
        .is_err()
    );
    assert!(
        Simulator::recover_reviewed(
            &data.restored.cases[index],
            &data.before.schema,
            ReviewedRecovery {
                release: data.release,
                publications: &history[..1],
                effects: RecoveryEvidence {
                    witness: &witness,
                    receipts: &receipts,
                    provider: &provider
                },
            },
        )
        .is_err()
    );
}

#[test]
#[ignore = "requires actual Lean Delta output; run just check-reviewed-effects"]
fn canonical_coverage_refuses_omission_duplication_substitution_and_relabeling() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/reviewed-effects/agent-payment-validated.json");
    let raw: Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let canonical = raw["original"].to_string();
    let document = crate::catalog_input::document(&canonical).unwrap();
    let bundle: Bundle = serde_json::from_value(raw.clone()).unwrap();
    super::coverage::check(&bundle, &document, "agent-payment-validated").unwrap();
    let edits: [fn(&mut Value); 4] = [
        |value| {
            value["groups"][0]["plan"]["stages"]["entries"]["before"]["cases"]
                .as_array_mut()
                .unwrap()
                .remove(0);
        },
        |value| {
            let group = value["groups"][0].clone();
            value["groups"].as_array_mut().unwrap().push(group);
        },
        |value| {
            value["groups"][0]["plan"]["stages"]["entries"]["before"]["cases"][0]["expected"] =
                serde_json::json!("substituted");
        },
        |value| {
            value["entry"] = serde_json::json!("another-domain");
        },
    ];
    for edit in edits {
        let mut changed = raw.clone();
        edit(&mut changed);
        let bundle: Bundle = serde_json::from_value(changed).unwrap();
        assert!(super::coverage::check(&bundle, &document, "agent-payment-validated").is_err());
    }
}
