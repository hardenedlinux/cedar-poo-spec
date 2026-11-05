use super::{actual, assert_locked, digest, verified};
use crate::gateway::checkpoint_store::CheckpointStage;
use crate::gateway::oauth::Grant;
use crate::gateway::oauth_refresh_durable::{
    DurableEffectRecovery, DurableEffectUse, DurableFinalUse, DurableRefreshLedger, EffectStatus,
    WriterCut,
};
use crate::gateway::provider_durable::{
    DurableReceiver, LegacyReceiverTrust, ReceiverCheckpoint, ReceiverCut, ReceiverDelivery,
    ReceiverDispatch, ReceiverTrust,
};
use crate::gateway::wire::{sign, simulation_key};
use crate::gateway::{
    AuditAuthority, EffectIdentity, FactAuthority, FactBinding, IntentAuditTrust, LogSnapshot,
    ProviderAuditTrust, ProviderJournal, ProviderOutcome, Reconciliation, Signed, Witness,
    WitnessFrontier, reconcile_intent, verify,
};
use cedar_poo_core::operation_identity::OperationId;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

const FIXTURE: &str = "CEDAR_OAUTH_LATE_BATCH_FIXTURE";
const PHASE: &str = "CEDAR_OAUTH_LATE_BATCH_PHASE";
const WORKER: &str = "gateway::oauth_refresh::tests::settlement::late_batch::restart_worker";

#[derive(Deserialize, Serialize)]
pub(super) struct RestartFixture {
    pub active: PathBuf,
    pub retired: PathBuf,
    pub writer: WriterCut,
    pub previous: ReceiverCheckpoint,
    pub fact: FactBinding,
    pub history: LogSnapshot,
    pub effect: EffectIdentity,
    pub missing: EffectIdentity,
    pub grant: Grant,
}

pub(super) fn replay_across_processes(
    root: &Path,
    mut fixture: RestartFixture,
    outcome: &Signed,
) -> (WriterCut, ReceiverCut) {
    let fixture_path = root.join("restart-fixture.json");
    let write_fixture = |fixture: &RestartFixture| {
        std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    };
    write_fixture(&fixture);
    finish_worker(spawn_worker(&fixture_path, "pending"), "pending");
    std::fs::write(
        root.join("late-envelope.json"),
        serde_json::to_vec(outcome).unwrap(),
    )
    .unwrap();
    let first = spawn_worker(&fixture_path, "commit");
    let second = spawn_worker(&fixture_path, "overlap");
    finish_worker(first, "commit");
    finish_worker(second, "overlap");

    let pin = root.join("pin");
    let sender = simulation_key(4);
    let provider = simulation_key(8);
    let witness = Witness::simulation().verifying_key();
    let trust = || ReceiverTrust {
        scope: "settlement-race",
        sender: sender.verifying_key(),
        witness: &witness,
        provider: &provider,
    };
    fixture.previous = DurableReceiver::managed(&fixture.active, &pin, trust())
        .unwrap()
        .acknowledged_checkpoint()
        .unwrap();
    std::fs::copy(
        fixture.active.join("checkpoint.json"),
        fixture.retired.join("checkpoint.json"),
    )
    .unwrap();
    let cut = DurableReceiver::managed(&fixture.retired, &pin, trust())
        .unwrap()
        .promote(&fixture.previous)
        .unwrap();
    let oauth_path = root.join("oauth");
    let open = || DurableRefreshLedger::new(&oauth_path, "settlement-race");
    let old_writer = open().for_writer(fixture.writer);
    fixture.writer = old_writer.rotate_writer().unwrap();
    let current = open().for_writer(fixture.writer);
    assert!(current.revoke(verified(digest())).unwrap());
    assert_eq!(
        old_writer.revoke(verified(digest())).unwrap_err(),
        "OAuth writer fenced"
    );
    std::mem::swap(&mut fixture.active, &mut fixture.retired);
    write_fixture(&fixture);
    finish_worker(spawn_worker(&fixture_path, "resumed"), "resumed");
    (fixture.writer, cut)
}

fn spawn_worker(fixture: &Path, phase: &str) -> Child {
    Command::new(std::env::current_exe().unwrap())
        .args(["--ignored", "--exact", WORKER])
        .env(FIXTURE, fixture)
        .env(PHASE, phase)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap()
}

fn wait_for_marker(path: &Path) {
    let start = Instant::now();
    while !path.exists() {
        assert!(
            start.elapsed() < Duration::from_secs(10),
            "waiting for {path:?}"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
}

fn finish_worker(child: Child, phase: &str) {
    let result = child.wait_with_output().unwrap();
    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(
        result.status.success() && stdout.contains("1 passed"),
        "{phase}\n{stdout}\n{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
#[ignore = "started as a fresh process by the settlement replay"]
fn restart_worker() {
    let Some(fixture_path) = std::env::var_os(FIXTURE).map(PathBuf::from) else {
        return;
    };
    let root = fixture_path.parent().unwrap();
    let fixture: RestartFixture =
        serde_json::from_slice(&std::fs::read(&fixture_path).unwrap()).unwrap();
    let oauth_path = root.join("oauth");
    let pin = root.join("pin");
    let oauth =
        DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
    let log_key = Witness::simulation().verifying_key();
    let sender = simulation_key(4);
    let provider = simulation_key(8);
    let issuer = simulation_key(3);
    let audit = AuditAuthority {
        gateway_key: *sender.verifying_key(),
        log_key,
        facts: FactAuthority::new(
            vec![fixture.fact.clone()],
            [(fixture.fact.issuer.clone(), *issuer.verifying_key())].into(),
            14,
        )
        .unwrap(),
        minimum_size: 1,
        independent_frontier: Some(
            WitnessFrontier::from_checkpoint(&fixture.history.checkpoint, &log_key).unwrap(),
        ),
        review_trust: None,
        prepared_publications: None,
    };
    let trust = ProviderAuditTrust {
        authority: &audit,
        provider_key: provider.verifying_key(),
    };
    let receiver_trust = || ReceiverTrust {
        scope: "settlement-race",
        sender: sender.verifying_key(),
        witness: &log_key,
        provider: &provider,
    };
    let receiver = DurableReceiver::managed(&fixture.active, &pin, receiver_trust()).unwrap();
    let trusted = LegacyReceiverTrust::from_config(&pin, "settlement-race").unwrap();
    let operation = OperationId(fixture.effect.operation.clone());
    let snapshot = || std::fs::read(oauth_path.join("checkpoint.json")).unwrap();
    let before = snapshot();
    let evidence = |journal, outcomes| DurableEffectRecovery {
        effect: &fixture.effect,
        journal,
        outcomes,
        history: &fixture.history,
        trust,
    };
    let phase = std::env::var(PHASE).unwrap();
    assert_eq!(
        oauth.effect_status(&operation).unwrap(),
        if phase == "resumed" {
            EffectStatus::Reconciled
        } else {
            EffectStatus::Unresolved
        }
    );

    let packet = root.join("late-envelope.json");
    if phase == "pending" {
        assert!(!packet.exists());
        let empty = ProviderJournal::default();
        let report = receiver.migrate_legacy_oauth_batch(&oauth, [evidence(&empty, &[])], &trusted);
        assert_eq!(report.pending, std::slice::from_ref(&operation));
        assert!(report.confirmed.is_empty() && report.stopped.is_none());
        assert_eq!(snapshot(), before);
        return;
    }
    let outcome: Signed = serde_json::from_slice(&std::fs::read(packet).unwrap()).unwrap();
    let decoded: ProviderOutcome = verify(&outcome, provider.verifying_key()).unwrap();
    let original = receiver.evidence(&operation).unwrap().unwrap();
    assert_eq!(outcome, original.outcome);
    let signed = [outcome];
    let retired = DurableReceiver::managed(&fixture.retired, &pin, receiver_trust()).unwrap();
    assert!(retired.promote(&fixture.previous).is_err());
    let stopped = retired
        .migrate_legacy_oauth_batch(&oauth, [evidence(&original.journal, &signed)], &trusted)
        .stopped
        .unwrap();
    assert_eq!(stopped.operation, operation);
    assert_eq!(
        stopped.error,
        "receiver replica differs from the independent checkpoint"
    );

    if phase == "commit" {
        let foreign_pin = root.join("restart-foreign-pin");
        std::fs::create_dir(&foreign_pin).unwrap();
        std::fs::copy(
            pin.join("checkpoint.json"),
            foreign_pin.join("checkpoint.json"),
        )
        .unwrap();
        let foreign =
            DurableReceiver::managed(&fixture.active, &foreign_pin, receiver_trust()).unwrap();
        let refused = foreign.migrate_legacy_oauth_batch(
            &oauth,
            [evidence(&original.journal, &signed)],
            &trusted,
        );
        assert_eq!(refused.pending, std::slice::from_ref(&operation));
        assert!(refused.confirmed.is_empty() && refused.stopped.is_none());
    }
    let mut conflict = decoded.clone();
    conflict.outcome.action.result = "different completion".into();
    let conflicting = [sign(&conflict, &provider).unwrap()];
    let journal = ProviderJournal::observation(conflict.outcome.action);
    assert_eq!(
        reconcile_intent(
            &journal,
            &conflicting,
            &fixture.history,
            IntentAuditTrust {
                authority: &audit,
                intent: &decoded.outcome.commit,
                provider_key: Some(provider.verifying_key()),
            }
        ),
        Reconciliation::default()
    );
    let original = || evidence(&original.journal, &signed);
    let conflict = evidence(&journal, &conflicting);
    let empty = ProviderJournal::default();
    let missing = DurableEffectRecovery {
        effect: &fixture.missing,
        ..evidence(&empty, &[])
    };
    let missing_operation = OperationId(fixture.missing.operation.clone());
    let ready = root.join("late-overlap-ready");
    let durable = root.join("late-original-durable");
    let contending = root.join("late-overlap-contending");

    if phase == "commit" {
        wait_for_marker(&ready);
        let report = receiver.migrate_legacy_oauth_batch_at(
            &oauth,
            [conflict, original(), original()],
            &trusted,
            |item, stage| {
                assert_eq!(item, &operation);
                if stage == CheckpointStage::Durable {
                    std::fs::write(&durable, []).unwrap();
                    wait_for_marker(&contending);
                    Err("late migration acknowledgment lost".into())
                } else {
                    Ok(())
                }
            },
        );
        assert!(report.confirmed.is_empty());
        assert_eq!(report.pending, std::slice::from_ref(&operation));
        let stopped = report.stopped.unwrap();
        assert_eq!(stopped.operation, operation);
        assert_eq!(stopped.error, "late migration acknowledgment lost");
        assert_ne!(snapshot(), before);
        return;
    }

    if phase == "overlap" {
        std::fs::write(ready, []).unwrap();
        wait_for_marker(&durable);
        assert_locked(&oauth_path);
        assert_locked(&pin);
        std::fs::write(contending, []).unwrap();
    } else {
        assert_eq!(phase, "resumed");
    }
    let committed = snapshot();
    let report = receiver.migrate_legacy_oauth_batch_at(
        &oauth,
        [original(), conflict, missing, original()],
        &trusted,
        |_, _| panic!("retry attempted a second migration write"),
    );
    assert_eq!(report.confirmed, [operation.clone(), operation.clone()]);
    assert_eq!(
        report.pending,
        [operation.clone(), missing_operation.clone()]
    );
    assert!(report.stopped.is_none());
    assert_eq!(snapshot(), committed);
    assert_eq!(
        oauth.effect_status(&operation).unwrap(),
        EffectStatus::Reconciled
    );
    assert_eq!(
        oauth.effect_status(&missing_operation).unwrap(),
        EffectStatus::Unresolved
    );
    if phase == "overlap" {
        return;
    }

    let intent = &decoded.outcome.commit;
    let dispatch =
        ReceiverDispatch::sign(receiver.cut().unwrap(), "late-retry", intent, &sender).unwrap();
    let checked = oauth.checkpoint().unwrap();
    let current = actual(fixture.grant, 14, "late-receipt-retry");
    let facts = [sign(&fixture.fact, &issuer).unwrap()];
    assert!(
        receiver
            .receive_oauth(
                &oauth,
                DurableEffectUse {
                    admission: DurableFinalUse {
                        checked: &checked,
                        replica: &checked,
                        current: &current,
                        base_allowed: true,
                    },
                    effect: &fixture.effect,
                    intent,
                    history: &fixture.history,
                    trust,
                },
                ReceiverDelivery {
                    authorization: &dispatch,
                    channel: "late-retry",
                    effect: &fixture.effect,
                    bindings: std::slice::from_ref(&fixture.fact),
                    facts: &facts,
                    publications: &[],
                },
            )
            .unwrap()
            .is_none()
    );
}
