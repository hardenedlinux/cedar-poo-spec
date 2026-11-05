use super::{
    FirstCommit, OwnedWorker, RecoveryRound, RestartFixture, assert_locked, run_worker,
    settled_batch, settlement_race, takeover, trace, wait_for_marker,
};
use crate::gateway::checkpoint_store::CheckpointStage;
use crate::gateway::oauth_refresh_durable::{DurableEffectRecovery, DurableRefreshLedger};
use crate::gateway::provider_durable::{
    DurableReceiver, LegacyReceiverTrust, ReceiverCut, ReceiverTrust,
};
use crate::gateway::wire::{sign, simulation_key};
use crate::gateway::{
    AuditAuthority, FactAuthority, ProviderAuditTrust, ProviderJournal, ProviderOutcome, Signed,
    Witness, WitnessFrontier, verify,
};
use cedar_poo_core::operation_identity::OperationId;
use std::path::Path;

#[test]
#[ignore = "explicit settled mapping crash replay under its own unchanged 120-second gate"]
fn trusted_settled_mapping_survives_restart_and_takeover() {
    settlement_race(
        "settled-mapping-restart",
        true,
        Some(FirstCommit::Migration),
        &[RecoveryRound::baseline()],
        Some(exercise),
    );
}

pub(super) fn exercise(root: &Path, fixture: &mut RestartFixture, outcome: &Signed) -> ReceiverCut {
    let initial_writer = fixture.writer.generation();
    let checkpoint = root.join("oauth/checkpoint.json");
    let fixture_path = root.join("restart-fixture.json");
    let mut legacy: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&checkpoint).unwrap()).unwrap();
    for effect in [&fixture.effect, &fixture.prefix] {
        let entry = legacy["effects"][&effect.operation]
            .as_object_mut()
            .unwrap();
        assert_eq!(entry["resolved"], true);
        assert!(entry.remove("receipt_identity").is_some());
    }
    legacy["effects"][&fixture.effect.operation]
        .as_object_mut()
        .unwrap()
        .remove("recovery_origin");
    std::fs::write(&checkpoint, serde_json::to_vec(&legacy).unwrap()).unwrap();
    std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    run_worker(&fixture_path, "settled-map-validate");
    // Missing original digest is missing evidence, not permission to invent it.
    let mut missing = legacy.clone();
    missing["effects"][&fixture.effect.operation]
        .as_object_mut()
        .unwrap()
        .remove("settled_outcome");
    std::fs::write(&checkpoint, serde_json::to_vec(&missing).unwrap()).unwrap();
    run_worker(&fixture_path, "settled-map-no-digest");
    let mut conflict = legacy.clone();
    conflict["effects"][&fixture.effect.operation]["settled_outcome"] = "wrong-digest".into();
    std::fs::write(&checkpoint, serde_json::to_vec(&conflict).unwrap()).unwrap();
    run_worker(&fixture_path, "settled-map-no-digest");
    std::fs::write(&checkpoint, serde_json::to_vec(&legacy).unwrap()).unwrap();
    let before = std::fs::read(&checkpoint).unwrap();
    let staged = OwnedWorker::spawn(&fixture_path, "settled-map-staged");
    wait_for_marker(&root.join("settled-map-staged-ready"));
    assert_locked(&root.join("oauth"));
    assert_locked(&root.join("pin"));
    staged.crash();
    assert_eq!(std::fs::read(&checkpoint).unwrap(), before);
    takeover(root, fixture);
    takeover(root, fixture);
    std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    let first = OwnedWorker::spawn(&fixture_path, "settled-map-durable");
    wait_for_marker(&root.join("settled-map-durable-staged"));
    let peer = OwnedWorker::spawn(&fixture_path, "settled-map-contender");
    wait_for_marker(&root.join("settled-map-contender-ready"));
    std::fs::write(root.join("settled-map-release"), []).unwrap();
    wait_for_marker(&root.join("settled-map-durable-ready"));
    assert_locked(&root.join("oauth"));
    assert_locked(&root.join("pin"));
    first.crash();
    peer.finish("settled-map-contender");
    let oauth_path = root.join("oauth");
    let oauth =
        DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
    let bound = oauth
        .effect_observation(&OperationId(fixture.effect.operation.clone()))
        .unwrap()
        .unwrap()
        .receipt_identity
        .unwrap();
    assert_eq!(bound.outcome, *outcome);
    let old = std::fs::read(&checkpoint).unwrap();
    run_worker(&fixture_path, "settled-map-confirm");
    assert_eq!(std::fs::read(&checkpoint).unwrap(), old);
    let mut cut = takeover(root, fixture);
    for _ in 0..4 {
        std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
        run_worker(&fixture_path, "settled-map-confirm");
        let mut observer = trace::RoundObserver::new(
            root,
            fixture,
            &RecoveryRound::baseline(),
            cut.generation,
            outcome,
        );
        observer.observe(fixture, "settled-map-confirmed", "both");
        observer.finish();
        cut = takeover(root, fixture);
    }
    std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    run_worker(&fixture_path, "settled-map-confirm");
    assert_eq!(fixture.writer.generation() - initial_writer, 7);
    eprintln!(
        "SETTLED-MAPPING-OK {}",
        serde_json::json!({
            "concurrent": true, "staged_crash": true, "lost_ack": true,
            "handoffs_before": 2, "handoffs_after": 5,
            "original_only": true, "missing_retained": true, "revoked_no_resend": true
        })
    );
    cut
}

pub(super) fn worker(root: &Path, fixture: &RestartFixture, phase: &str) {
    if phase == "settled-map-contender" {
        std::fs::write(root.join("settled-map-contender-ready"), []).unwrap();
    }

    let sender = simulation_key(4);
    let provider = simulation_key(8);
    let witness = Witness::simulation().verifying_key();
    let issuer = simulation_key(3);
    let audit = AuditAuthority {
        gateway_key: *sender.verifying_key(),
        log_key: witness,
        facts: FactAuthority::new(
            vec![fixture.fact.clone()],
            [(fixture.fact.issuer.clone(), *issuer.verifying_key())].into(),
            14,
        )
        .unwrap(),
        minimum_size: 1,
        independent_frontier: Some(
            WitnessFrontier::from_checkpoint(&fixture.history.checkpoint, &witness).unwrap(),
        ),
        review_trust: None,
        prepared_publications: None,
    };
    let pin = root.join("pin");
    let trust = || ReceiverTrust {
        scope: "settlement-race",
        sender: sender.verifying_key(),
        witness: &witness,
        provider: &provider,
    };
    let receiver = DurableReceiver::managed(&fixture.active, &pin, trust()).unwrap();
    let retired = DurableReceiver::managed(&fixture.retired, &pin, trust()).unwrap();
    let configured = LegacyReceiverTrust::from_config(&pin, "settlement-race").unwrap();
    let oauth_path = root.join("oauth");
    let oauth =
        DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
    let operation = OperationId(fixture.effect.operation.clone());
    let prefix_operation = OperationId(fixture.prefix.operation.clone());
    let original = receiver.evidence(&operation).unwrap().unwrap();
    let prefix = receiver.evidence(&prefix_operation).unwrap().unwrap();
    let outcomes = [original.outcome.clone()];
    let prefix_outcomes = [prefix.outcome.clone()];
    let decoded: ProviderOutcome = verify(&outcomes[0], provider.verifying_key()).unwrap();
    let mut altered = decoded.clone();
    altered.outcome.action.result = "conflicting completion".into();
    let conflict = [sign(&altered, &provider).unwrap()];
    let conflict_journal = ProviderJournal::observation(altered.outcome.action);
    let empty = ProviderJournal::default();
    let evidence = |effect, journal, receipts| DurableEffectRecovery {
        effect,
        journal,
        outcomes: receipts,
        history: &fixture.history,
        trust: ProviderAuditTrust {
            authority: &audit,
            provider_key: provider.verifying_key(),
        },
    };
    let input = || evidence(&fixture.effect, &original.journal, &outcomes);
    let checkpoint = oauth_path.join("checkpoint.json");
    let before = std::fs::read(&checkpoint).unwrap();
    if phase == "settled-map-no-digest" {
        let report = receiver.migrate_settled_oauth_mappings(&oauth, [input()], &configured);
        assert_eq!(report.pending, [operation]);
        assert!(report.confirmed.is_empty() && report.stopped.is_none());
        assert_eq!(std::fs::read(&checkpoint).unwrap(), before);
        return;
    }
    if phase == "settled-map-validate" {
        let ordinary = receiver.migrate_legacy_oauth_batch(&oauth, [input()], &configured);
        assert!(ordinary.confirmed.is_empty());
        let report = receiver.migrate_settled_oauth_mappings(
            &oauth,
            [
                evidence(&fixture.effect, &empty, &[]),
                evidence(&fixture.effect, &conflict_journal, &conflict),
                evidence(&fixture.effect, &prefix.journal, &prefix_outcomes),
                evidence(&fixture.missing, &original.journal, &outcomes),
            ],
            &configured,
        );
        assert!(report.confirmed.is_empty() && report.stopped.is_none());
        assert_eq!(report.pending.len(), 4);
        let foreign_dir = root.join("settled-map-foreign");
        std::fs::create_dir_all(&foreign_dir).unwrap();
        let foreign = LegacyReceiverTrust::from_config(&foreign_dir, "settlement-race").unwrap();
        assert!(
            receiver
                .migrate_settled_oauth_mappings(&oauth, [input()], &foreign)
                .confirmed
                .is_empty()
        );
        let foreign_provider = simulation_key(9);
        let foreign_source = [sign(&decoded, &foreign_provider).unwrap()];
        let wrong_root = DurableEffectRecovery {
            outcomes: &foreign_source,
            trust: ProviderAuditTrust {
                authority: &audit,
                provider_key: foreign_provider.verifying_key(),
            },
            ..input()
        };
        assert!(
            receiver
                .migrate_settled_oauth_mappings(&oauth, [wrong_root], &configured)
                .confirmed
                .is_empty()
        );
        assert_eq!(std::fs::read(&checkpoint).unwrap(), before);
        return;
    }
    assert!(
        receiver
            .migrate_settled_oauth_mappings(
                &oauth.for_writer(fixture.retired_writer.unwrap()),
                [input()],
                &configured
            )
            .stopped
            .is_some()
    );
    assert!(
        retired
            .migrate_settled_oauth_mappings(&oauth, [input()], &configured)
            .stopped
            .is_some()
    );
    if phase.starts_with("settled-batch-") {
        let mut batch = vec![input()];
        if phase.ends_with("-a") {
            batch.push(evidence(&fixture.prefix, &empty, &[]));
            batch.push(evidence(&fixture.effect, &conflict_journal, &conflict));
        } else {
            batch.push(evidence(&fixture.effect, &conflict_journal, &conflict));
            batch.push(evidence(&fixture.prefix, &empty, &[]));
        }
        batch.push(input());
        settled_batch::worker(root, fixture, phase, &receiver, &oauth, &configured, batch);
        return;
    }
    let batch = if phase == "settled-map-staged" || phase == "settled-map-durable" {
        vec![input()]
    } else {
        vec![
            evidence(&fixture.effect, &conflict_journal, &conflict),
            input(),
            evidence(&fixture.prefix, &prefix.journal, &prefix_outcomes),
            evidence(&fixture.missing, &empty, &[]),
            input(),
        ]
    };
    let report =
        receiver.migrate_settled_oauth_mappings_at(&oauth, batch, &configured, |_, stage| {
            if phase == "settled-map-confirm" {
                panic!("idempotent confirmation wrote");
            }
            if phase == "settled-map-staged" && stage == CheckpointStage::Staged {
                std::fs::write(root.join("settled-map-staged-ready"), []).unwrap();
                loop {
                    std::thread::park();
                }
            }
            if phase == "settled-map-durable" {
                if stage == CheckpointStage::Staged {
                    std::fs::write(root.join("settled-map-durable-staged"), []).unwrap();
                    wait_for_marker(&root.join("settled-map-release"));
                } else {
                    std::fs::write(root.join("settled-map-durable-ready"), []).unwrap();
                    loop {
                        std::thread::park();
                    }
                }
            }
            Ok(())
        });
    assert!(report.stopped.is_none());
    assert_eq!(
        report.confirmed,
        [operation.clone(), prefix_operation, operation.clone()]
    );
    assert_eq!(
        report.pending,
        [operation, OperationId(fixture.missing.operation.clone())]
    );
    if phase == "settled-map-confirm" {
        assert_eq!(std::fs::read(&checkpoint).unwrap(), before);
    }
}
