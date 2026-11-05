use super::{
    FirstCommit, OwnedWorker, RecoveryRound, RestartFixture, digest, run_worker, settlement_race,
    takeover, trace, verified, wait_for_marker,
};
use crate::gateway::Signed;
use crate::gateway::checkpoint_store::CheckpointStage;
use crate::gateway::oauth_refresh_durable::{DurableEffectRecovery, DurableRefreshLedger};
use crate::gateway::provider_durable::{DurableReceiver, LegacyReceiverTrust, ReceiverCut};
use cedar_poo_core::operation_identity::OperationId;
use std::path::Path;

#[test]
#[ignore = "settled overlapping batch interruption replay under the original 120-second gate"]
fn overlapping_settled_batches_resume_from_durable_progress() {
    settlement_race(
        "settled-batch-resume",
        true,
        Some(FirstCommit::Migration),
        &[RecoveryRound::baseline()],
        Some(exercise),
    );
}

pub(super) fn exercise(
    root: &Path,
    fixture: &mut RestartFixture,
    original: &Signed,
) -> ReceiverCut {
    let start = fixture.writer.generation();
    let checkpoint = root.join("oauth/checkpoint.json");
    let fixture_path = root.join("restart-fixture.json");
    let mut legacy: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&checkpoint).unwrap()).unwrap();
    for effect in [&fixture.effect, &fixture.prefix] {
        let row = legacy["effects"][&effect.operation]
            .as_object_mut()
            .unwrap();
        assert!(row.remove("receipt_identity").is_some());
    }
    assert!(
        legacy["effects"][&fixture.effect.operation]
            .as_object_mut()
            .unwrap()
            .remove("recovery_origin")
            .is_some()
    );
    // Historical fixture before revocation; no production rollback API is used.
    for pair in legacy["checkpoint"]["ledger"]["families"]
        .as_array_mut()
        .unwrap()
    {
        assert_eq!(pair[1]["revoked"], true);
        pair[1]["revoked"] = false.into();
    }
    std::fs::write(&checkpoint, serde_json::to_vec(&legacy).unwrap()).unwrap();
    std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    let first = OwnedWorker::spawn(&fixture_path, "settled-batch-commit-a");
    wait_for_marker(&root.join("settled-batch-committed"));
    let peer = OwnedWorker::spawn(&fixture_path, "settled-batch-commit-b");
    first.crash();
    wait_for_marker(&root.join("settled-batch-prefix-b"));
    let restarted = OwnedWorker::spawn(&fixture_path, "settled-batch-pause-a");
    wait_for_marker(&root.join("settled-batch-prefix-a"));
    let oauth_path = root.join("oauth");
    let current =
        DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
    let prefix = OperationId(fixture.prefix.operation.clone());
    let operation = OperationId(fixture.effect.operation.clone());
    let pending = current.settled_unmapped_operations().unwrap();
    assert!(pending.contains(&prefix) && !pending.contains(&operation));
    assert_eq!(
        current
            .effect_observation(&operation)
            .unwrap()
            .unwrap()
            .receipt_identity
            .unwrap()
            .outcome,
        *original
    );
    takeover(root, fixture);
    let current =
        DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
    let before = serde_json::to_value(current.checkpoint().unwrap()).unwrap();
    assert!(current.revoke(verified(digest())).unwrap());
    let after = serde_json::to_value(current.checkpoint().unwrap()).unwrap();
    assert_eq!(
        after["ledger"]["position"].as_u64().unwrap(),
        before["ledger"]["position"].as_u64().unwrap() + 1
    );
    takeover(root, fixture);
    let after_handoff = std::fs::read(&checkpoint).unwrap();
    std::fs::write(root.join("settled-batch-continue"), []).unwrap();
    restarted.finish("settled-batch-pause-a");
    peer.finish("settled-batch-commit-b");
    assert_eq!(std::fs::read(&checkpoint).unwrap(), after_handoff);
    std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    run_worker(&fixture_path, "settled-batch-resume-b");
    let confirmation = OwnedWorker::spawn(&fixture_path, "settled-batch-ack-lost-a");
    wait_for_marker(&root.join("settled-batch-confirmed"));
    confirmation.crash();
    assert_eq!(std::fs::read(&checkpoint).unwrap(), after_handoff);
    for round in 0..5 {
        let cut = takeover(root, fixture);
        std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
        run_worker(
            &fixture_path,
            if round % 2 == 0 {
                "settled-batch-resume-a"
            } else {
                "settled-batch-resume-b"
            },
        );
        let mut observer = trace::RoundObserver::new(
            root,
            fixture,
            &RecoveryRound::baseline(),
            cut.generation,
            original,
        );
        observer.observe(fixture, "settled-batch-resumed", "both");
        observer.finish();
        let current =
            DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
        assert!(
            current
                .settled_unmapped_operations()
                .unwrap()
                .contains(&prefix)
        );
        assert!(
            current
                .effect_observation(&prefix)
                .unwrap()
                .unwrap()
                .receipt_identity
                .is_none()
        );
    }
    assert_eq!(fixture.writer.generation() - start, 7);
    let sender = crate::gateway::wire::simulation_key(4);
    let provider = crate::gateway::wire::simulation_key(8);
    let witness = crate::gateway::Witness::simulation().verifying_key();
    let pin = root.join("pin");
    let active = DurableReceiver::managed(
        &fixture.active,
        &pin,
        crate::gateway::provider_durable::ReceiverTrust {
            scope: "settlement-race",
            sender: sender.verifying_key(),
            witness: &witness,
            provider: &provider,
        },
    )
    .unwrap();
    eprintln!(
        "SETTLED-BATCH-OK {}",
        serde_json::json!({
            "overlapping_workers": 2, "durable_ack_lost": true, "confirmation_lost": true,
            "fenced_suffixes": 2, "handoffs": 7, "revocation_advanced": true,
            "durable_discovery": true, "missing_retained": true, "original_idempotent": true,
            "conflict_refused": true, "no_resend": true
        })
    );
    active.cut().unwrap()
}

pub(super) fn worker<'a>(
    root: &Path,
    fixture: &RestartFixture,
    phase: &str,
    receiver: &DurableReceiver<'_>,
    oauth: &DurableRefreshLedger<'_>,
    trusted: &LegacyReceiverTrust,
    items: Vec<DurableEffectRecovery<'a>>,
) {
    let operation = OperationId(fixture.effect.operation.clone());
    let prefix = OperationId(fixture.prefix.operation.clone());
    let checkpoint = root.join("oauth/checkpoint.json");
    let before = std::fs::read(&checkpoint).unwrap();
    let paused = phase == "settled-batch-pause-a" || phase == "settled-batch-commit-b";
    let stream = items.into_iter().enumerate().map(|(index, item)| {
        if index == 1 && paused {
            let role = if phase.ends_with("-a") { "a" } else { "b" };
            std::fs::write(root.join(format!("settled-batch-prefix-{role}")), []).unwrap();
            wait_for_marker(&root.join("settled-batch-continue"));
        }
        item
    });
    let report = receiver.migrate_settled_oauth_mappings_at(oauth, stream, trusted, |_, stage| {
        if phase == "settled-batch-commit-a" && stage == CheckpointStage::Durable {
            std::fs::write(root.join("settled-batch-committed"), []).unwrap();
            loop {
                std::thread::park();
            }
        }
        if phase.starts_with("settled-batch-resume-") || phase == "settled-batch-ack-lost-a" {
            panic!("resumed batch rewrote a committed or missing-evidence row");
        }
        Ok(())
    });
    if paused {
        assert_eq!(report.confirmed, std::slice::from_ref(&operation));
        assert!(report.pending.is_empty());
        let stopped = report.stopped.unwrap();
        assert_eq!(stopped.error, "OAuth writer fenced");
        assert_eq!(
            stopped.operation,
            if phase.ends_with("-a") {
                prefix
            } else {
                operation
            }
        );
        return;
    }
    assert!(report.stopped.is_none());
    assert_eq!(report.confirmed, [operation.clone(), operation.clone()]);
    assert_eq!(
        report.pending,
        if phase.ends_with("-a") {
            vec![prefix, operation]
        } else {
            vec![operation, prefix]
        }
    );
    assert_eq!(std::fs::read(&checkpoint).unwrap(), before);
    if phase == "settled-batch-ack-lost-a" {
        std::fs::write(root.join("settled-batch-confirmed"), []).unwrap();
        loop {
            std::thread::park();
        }
    }
}
