use super::{OwnedWorker, RestartFixture, run_worker, takeover, wait_for_marker};
use crate::gateway::checkpoint_store::CheckpointStage;
use crate::gateway::oauth_refresh_durable::{DurableEffectRecovery, DurableRefreshLedger};
use crate::gateway::provider_durable::{DurableReceiver, LegacyReceiverTrust, ReceiverCut};
use crate::gateway::wire::{sign, simulation_key};
use crate::gateway::{ProviderOutcome, Signed, verify};
use cedar_poo_core::operation_identity::OperationId;
use std::path::Path;

pub(super) fn exercise(
    root: &Path,
    fixture: &mut RestartFixture,
    first: &Signed,
    delayed: &Signed,
) -> ReceiverCut {
    let before_writer = fixture.writer.generation();
    let oauth_path = root.join("oauth");
    let checkpoint = oauth_path.join("checkpoint.json");
    let operation = OperationId(fixture.prefix.operation.clone());
    let first_operation = OperationId(fixture.effect.operation.clone());
    let current =
        DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
    assert!(
        current
            .settled_unmapped_operations()
            .unwrap()
            .contains(&operation)
    );
    let initial = current.effect_observation(&operation).unwrap().unwrap();
    assert!(initial.receipt_identity.is_none());
    let old_digest = initial.outcome_identity.unwrap();
    let original: ProviderOutcome = verify(delayed, simulation_key(8).verifying_key()).unwrap();
    let mut conflict = original;
    conflict.outcome.action.result = "conflicting delayed completion".into();
    let conflicting = sign(&conflict, &simulation_key(8)).unwrap();
    assert_ne!(conflicting.source_sha256().unwrap(), old_digest);
    std::fs::write(
        root.join("settled-late-receipts.json"),
        serde_json::to_vec(&[conflicting, delayed.clone(), delayed.clone(), first.clone()])
            .unwrap(),
    )
    .unwrap();
    let fixture_path = root.join("restart-fixture.json");
    std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    let winner = OwnedWorker::spawn(&fixture_path, "settled-late-first-a");
    wait_for_marker(&root.join("settled-late-committed"));
    let peer = OwnedWorker::spawn(&fixture_path, "settled-late-peer-b");
    winner.crash();
    peer.finish("settled-late-peer-b");
    let current =
        DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
    let bound = current
        .effect_observation(&operation)
        .unwrap()
        .unwrap()
        .receipt_identity
        .unwrap();
    assert_eq!(bound.outcome, *delayed);
    assert_eq!(bound.identity.outcome_sha256, old_digest);
    assert!(
        !current
            .settled_unmapped_operations()
            .unwrap()
            .contains(&operation)
    );
    let stable = std::fs::read(&checkpoint).unwrap();
    let lost = OwnedWorker::spawn(&fixture_path, "settled-late-ack-a");
    wait_for_marker(&root.join("settled-late-confirmed"));
    lost.crash();
    assert_eq!(std::fs::read(&checkpoint).unwrap(), stable);
    let mut cut = takeover(root, fixture);
    for role in ["a", "b"] {
        std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
        run_worker(&fixture_path, &format!("settled-late-confirm-{role}"));
        let current =
            DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
        assert_eq!(
            current
                .effect_observation(&operation)
                .unwrap()
                .unwrap()
                .receipt_identity
                .as_ref(),
            Some(&bound)
        );
        assert_eq!(
            current
                .effect_observation(&first_operation)
                .unwrap()
                .unwrap()
                .receipt_identity
                .unwrap()
                .outcome,
            *first
        );
        assert!(
            !current
                .settled_unmapped_operations()
                .unwrap()
                .contains(&operation)
        );
        cut = takeover(root, fixture);
    }
    std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    run_worker(&fixture_path, "settled-late-confirm-a");
    let later_handoffs = fixture.writer.generation() - before_writer;
    assert_eq!(later_handoffs, 3);
    eprintln!(
        "SETTLED-LATE-OK {}",
        serde_json::json!({
            "previous_handoffs": 7, "later_handoffs": later_handoffs, "workers": 2,
            "out_of_order": true, "duplicates_idempotent": true, "conflicts_refused": true,
            "original_digest_retained": true, "durable_ack_lost": true,
            "confirmation_lost": true, "pending_discovery_cleared": true,
            "revoked_no_resend": true
        })
    );
    cut
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
    let operation = OperationId(fixture.prefix.operation.clone());
    let first = OperationId(fixture.effect.operation.clone());
    let before = std::fs::read(root.join("oauth/checkpoint.json")).unwrap();
    let report = receiver.migrate_settled_oauth_mappings_at(oauth, items, trusted, |_, stage| {
        if phase == "settled-late-first-a" {
            if stage == CheckpointStage::Durable {
                std::fs::write(root.join("settled-late-committed"), []).unwrap();
                loop {
                    std::thread::park();
                }
            }
        } else {
            panic!("late duplicate or conflict rewrote a mapping");
        }
        Ok(())
    });
    assert!(report.stopped.is_none());
    assert_eq!(report.pending, std::slice::from_ref(&operation));
    assert_eq!(
        report.confirmed,
        if phase.ends_with("-a") {
            vec![operation.clone(), operation, first]
        } else {
            vec![first, operation.clone(), operation]
        }
    );
    assert_eq!(
        std::fs::read(root.join("oauth/checkpoint.json")).unwrap(),
        before
    );
    if phase == "settled-late-ack-a" {
        std::fs::write(root.join("settled-late-confirmed"), []).unwrap();
        loop {
            std::thread::park();
        }
    }
    // Revocation and stable operation reservation still govern all effect use.
    let current = super::actual(fixture.grant.clone(), 14, &format!("late-{phase}"));
    let checked = oauth.checkpoint().unwrap();
    assert!(
        !oauth
            .execute_final(
                crate::gateway::oauth_refresh_durable::DurableFinalUse {
                    checked: &checked,
                    replica: &checked,
                    current: &current,
                    base_allowed: true,
                },
                || panic!("late receipt authorized a new effect")
            )
            .unwrap()
    );
}
