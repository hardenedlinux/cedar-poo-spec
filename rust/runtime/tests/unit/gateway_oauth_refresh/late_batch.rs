use super::{actual, assert_locked, digest, settlement_race, verified};
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

#[path = "settled_mapping.rs"]
mod settled_mapping;
#[path = "recovery_trace.rs"]
mod trace;
pub(super) use trace::{RecoveryRound, Worker};

const FIXTURE: &str = "CEDAR_OAUTH_LATE_BATCH_FIXTURE";
const PHASE: &str = "CEDAR_OAUTH_LATE_BATCH_PHASE";
const WORKER: &str = "gateway::oauth_refresh::tests::settlement::late_batch::restart_worker";

#[derive(Deserialize, Serialize)]
pub(super) struct RestartFixture {
    pub active: PathBuf,
    pub retired: PathBuf,
    pub writer: WriterCut,
    pub retired_writer: Option<WriterCut>,
    pub previous: ReceiverCheckpoint,
    pub fact: FactBinding,
    pub history: LogSnapshot,
    pub effect: EffectIdentity,
    pub prefix: EffectIdentity,
    pub missing: EffectIdentity,
    pub missing_intent: Signed,
    pub grant: Grant,
    pub round: usize,
    pub first_worker: Worker,
}

#[derive(Clone, Copy)]
pub(super) enum FirstCommit {
    Takeover,
    Migration,
}

#[test]
fn legacy_migration_takeover_first_fences_batch_suffix() {
    super::settlement_race(
        "legacy-handoff-first",
        true,
        Some(FirstCommit::Takeover),
        &[RecoveryRound::baseline()],
        false,
    );
}

#[test]
fn legacy_migration_commit_first_survives_revoked_batch_takeover() {
    super::settlement_race(
        "legacy-commit-first",
        true,
        Some(FirstCommit::Migration),
        &[RecoveryRound::baseline()],
        false,
    );
}

pub(super) fn replay_across_processes(
    root: &Path,
    mut fixture: RestartFixture,
    outcome: &Signed,
    first: FirstCommit,
    rounds: &[RecoveryRound],
    settled_backfill: bool,
) -> (WriterCut, ReceiverCut, PathBuf) {
    let fixture_path = root.join("restart-fixture.json");
    let write_fixture = |fixture: &RestartFixture| {
        std::fs::write(&fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    };
    let packet = root.join("late-envelope.json");
    let publish = || std::fs::write(&packet, serde_json::to_vec(outcome).unwrap()).unwrap();
    write_fixture(&fixture);
    run_worker(&fixture_path, "pending");
    publish();

    let checkpoint = root.join("oauth/checkpoint.json");
    let staged = root.join("oauth/checkpoint.staged");
    let before = std::fs::read(&checkpoint).unwrap();
    let (crashing, overlap) = start_crash_race(&fixture_path, "staged", "staged-overlap");
    kill_worker(crashing);
    finish_worker(overlap, "staged-overlap");
    assert_eq!(std::fs::read(&checkpoint).unwrap(), before);
    assert_ne!(std::fs::read(&staged).unwrap(), before);
    takeover(root, &mut fixture);
    write_fixture(&fixture);
    run_worker(&fixture_path, "fenced");
    std::fs::remove_file(&packet).unwrap();
    run_worker(&fixture_path, "pending");

    publish();
    let (worker, phase, expected) = match first {
        FirstCommit::Takeover => (
            spawn_worker(&fixture_path, "takeover-first"),
            "takeover-first",
            EffectStatus::Unresolved,
        ),
        FirstCommit::Migration => {
            let (crashing, overlap) = start_crash_race(&fixture_path, "durable", "durable-overlap");
            kill_worker(crashing);
            assert!(!staged.exists());
            (overlap, "durable-overlap", EffectStatus::Reconciled)
        }
    };
    wait_for_marker(&root.join("between-items"));
    let peer_phase = match first {
        FirstCommit::Takeover => "peer-takeover",
        FirstCommit::Migration => "peer-migration",
    };
    let peer = spawn_worker(&fixture_path, peer_phase);
    wait_for_marker(&root.join("peer-between-items"));
    let oauth_path = root.join("oauth");
    let oauth = DurableRefreshLedger::new(&oauth_path, "settlement-race");
    let operation = OperationId(fixture.effect.operation.clone());
    assert_eq!(
        oauth
            .for_writer(fixture.writer)
            .effect_status(&operation)
            .unwrap(),
        expected
    );
    takeover(root, &mut fixture);
    assert!(
        oauth
            .for_writer(fixture.writer)
            .revoke(verified(digest()))
            .unwrap()
    );
    takeover(root, &mut fixture);
    let checkpoint_after_takeover = std::fs::read(&checkpoint).unwrap();
    std::fs::write(root.join("resume-items"), []).unwrap();
    finish_worker(worker, phase);
    finish_worker(peer, peer_phase);
    assert_eq!(
        std::fs::read(&checkpoint).unwrap(),
        checkpoint_after_takeover
    );
    let current = oauth.for_writer(fixture.writer);
    assert_eq!(current.effect_status(&operation).unwrap(), expected);
    write_fixture(&fixture);

    if matches!(first, FirstCommit::Takeover) {
        run_worker(&fixture_path, "fenced");
        std::fs::remove_file(&packet).unwrap();
        run_worker(&fixture_path, "pending");
        publish();
        run_worker(&fixture_path, "rebind");
    }
    // Recovery starts from the committed receipt even when its acknowledgment was lost.
    let mut cut = takeover(root, &mut fixture);
    assert!(!rounds.is_empty());
    for (index, round) in rounds.iter().enumerate() {
        fixture.round = index;
        fixture.first_worker = round.first_worker;
        let signals = root.join(format!("recovery-round-{index}"));
        std::fs::create_dir(&signals).unwrap();
        write_fixture(&fixture);
        let before_writer = fixture.writer.generation();
        let before_receiver = cut.generation;
        let mut observer =
            trace::RoundObserver::new(root, &fixture, round, before_receiver, outcome);
        cut = replay_round(root, &fixture_path, &mut fixture, round, &mut observer);
        observer.finish();
        assert_eq!(
            fixture.writer.generation() - before_writer,
            round.expected_advances
        );
        assert_eq!(cut.generation - before_receiver, round.expected_advances);
        eprintln!(
            "RECOVERY-ROUND-OK {}",
            serde_json::json!({
                "order": match first { FirstCommit::Takeover => "takeover-first", FirstCommit::Migration => "migration-first" },
                "round": index,
                "writer_advances": fixture.writer.generation() - before_writer,
                "receiver_advances": cut.generation - before_receiver,
                "crashes": round.expected_crashes
            })
        );
    }
    if settled_backfill {
        cut = settled_mapping::exercise(root, &mut fixture, outcome);
    }
    (fixture.writer, cut, fixture.active)
}

fn replay_round(
    root: &Path,
    fixture_path: &Path,
    fixture: &mut RestartFixture,
    round: &RecoveryRound,
    observer: &mut trace::RoundObserver,
) -> ReceiverCut {
    let checkpoint = root.join("oauth/checkpoint.json");
    let signals = root.join(format!("recovery-round-{}", fixture.round));
    let write_fixture = |fixture: &RestartFixture| {
        std::fs::write(fixture_path, serde_json::to_vec(fixture).unwrap()).unwrap();
    };
    let mut crashes = 0;
    let before_recovery = std::fs::read(&checkpoint).unwrap();
    observer.observe(fixture, "ready", "both");
    let first_phase = fixture.first_worker.phase("resumed");
    let second_phase = fixture.first_worker.other().phase("resumed");
    let first = spawn_worker(fixture_path, &first_phase);
    let second = spawn_worker(fixture_path, &second_phase);
    wait_for_marker(&signals.join("recovery-paused-resumed-a"));
    wait_for_marker(&signals.join("recovery-paused-resumed-b"));
    assert_eq!(std::fs::read(&checkpoint).unwrap(), before_recovery);
    kill_worker(first);
    crashes += 1;
    assert_eq!(std::fs::read(&checkpoint).unwrap(), before_recovery);
    observer.observe(fixture, "worker-crash", fixture.first_worker.name());
    takeovers(root, fixture, round.handoffs_after_first, observer);
    let after_recovery_takeover = std::fs::read(&checkpoint).unwrap();
    std::fs::write(signals.join("recovery-continue"), []).unwrap();
    wait_for_marker(&signals.join("recovery-second-fenced"));
    assert_eq!(std::fs::read(&checkpoint).unwrap(), after_recovery_takeover);
    observer.observe(fixture, "fenced", fixture.first_worker.other().name());
    kill_worker(second);
    crashes += 1;
    assert_eq!(std::fs::read(&checkpoint).unwrap(), after_recovery_takeover);
    observer.observe(fixture, "worker-crash", fixture.first_worker.other().name());

    takeovers(root, fixture, round.handoffs_after_second, observer);
    write_fixture(fixture);
    let before_confirmation = std::fs::read(&checkpoint).unwrap();
    let confirmation_phase = fixture.first_worker.phase("ack-lost");
    let peer_phase = fixture.first_worker.other().phase("ack-lost");
    let confirmation = spawn_worker(fixture_path, &confirmation_phase);
    let peer = spawn_worker(fixture_path, &peer_phase);
    wait_for_marker(&signals.join("confirmation-verified"));
    finish_worker(peer, &peer_phase);
    assert_eq!(std::fs::read(&checkpoint).unwrap(), before_confirmation);
    observer.observe(fixture, "confirmed", "both");
    kill_worker(confirmation);
    crashes += 1;
    assert_eq!(std::fs::read(&checkpoint).unwrap(), before_confirmation);
    observer.observe(fixture, "confirmation-lost", fixture.first_worker.name());

    let cut = takeovers(root, fixture, round.handoffs_after_confirmation, observer);
    write_fixture(fixture);
    let after_confirmation_takeover = std::fs::read(&checkpoint).unwrap();
    let first = spawn_worker(fixture_path, "recovered-a");
    let second = spawn_worker(fixture_path, "recovered-b");
    finish_worker(first, "recovered-a");
    finish_worker(second, "recovered-b");
    assert_eq!(
        std::fs::read(&checkpoint).unwrap(),
        after_confirmation_takeover
    );
    observer.observe(fixture, "recovered", "both");
    assert_eq!(crashes, round.expected_crashes);
    cut
}

fn takeovers(
    root: &Path,
    fixture: &mut RestartFixture,
    count: u64,
    observer: &mut trace::RoundObserver,
) -> ReceiverCut {
    assert!(count > 0);
    let mut cut = takeover(root, fixture);
    observer.observe(fixture, "handoff", "authority");
    for _ in 1..count {
        cut = takeover(root, fixture);
        observer.observe(fixture, "handoff", "authority");
    }
    cut
}

fn takeover(root: &Path, fixture: &mut RestartFixture) -> ReceiverCut {
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
    let standby = DurableReceiver::managed(&fixture.retired, &pin, trust()).unwrap();
    let oauth_path = root.join("oauth");
    let old_writer =
        DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
    assert_eq!(
        standby.cut().unwrap_err(),
        "receiver replica has not been promoted"
    );
    let cut = standby.promote(&fixture.previous).unwrap();
    fixture.retired_writer = Some(fixture.writer);
    fixture.writer = old_writer.rotate_writer().unwrap();
    assert_eq!(
        old_writer.revoke(verified(digest())).unwrap_err(),
        "OAuth writer fenced"
    );
    std::mem::swap(&mut fixture.active, &mut fixture.retired);
    cut
}

fn start_crash_race(fixture: &Path, phase: &str, overlap_phase: &str) -> (Child, Child) {
    let markers = fixture.parent().unwrap().join(phase);
    std::fs::create_dir(&markers).unwrap();
    let crashing = spawn_worker(fixture, phase);
    let overlap = spawn_worker(fixture, overlap_phase);
    wait_for_marker(&markers.join("contending"));
    (crashing, overlap)
}

fn kill_worker(mut crashing: Child) {
    crashing.kill().unwrap();
    let status = crashing.wait().unwrap();
    assert!(!status.success());
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(status.signal(), Some(9));
    }
}

fn run_worker(fixture: &Path, phase: &str) {
    finish_worker(spawn_worker(fixture, phase), phase);
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
    let requested = std::env::var(PHASE).unwrap();
    if requested.starts_with("settled-map-") {
        settled_mapping::worker(root, &fixture, &requested);
        return;
    }
    let signals = root.join(format!("recovery-round-{}", fixture.round));
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
        if phase.starts_with("resumed-")
            || phase.starts_with("recovered-")
            || phase.starts_with("ack-lost-")
            || phase == "peer-migration"
        {
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
    let assert_no_resend = |effect: &EffectIdentity, intent: &Signed, proof: &str| {
        let dispatch =
            ReceiverDispatch::sign(receiver.cut().unwrap(), "late-retry", intent, &sender).unwrap();
        let checked = oauth.checkpoint().unwrap();
        let current = actual(
            fixture.grant.clone(),
            14,
            &format!("round-{}-{phase}-{proof}", fixture.round),
        );
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
                        effect,
                        intent,
                        history: &fixture.history,
                        trust,
                    },
                    ReceiverDelivery {
                        authorization: &dispatch,
                        channel: "late-retry",
                        effect,
                        bindings: std::slice::from_ref(&fixture.fact),
                        facts: &facts,
                        publications: &[],
                    },
                )
                .unwrap()
                .is_none()
        );
    };
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

    if phase == "fenced"
        || phase.starts_with("resumed-")
        || phase.starts_with("recovered-")
        || phase.starts_with("ack-lost-")
    {
        let old_writer = oauth.for_writer(fixture.retired_writer.unwrap());
        let stopped = receiver
            .migrate_legacy_oauth_batch(
                &old_writer,
                [evidence(&original.journal, &signed)],
                &trusted,
            )
            .stopped
            .unwrap();
        assert_eq!(stopped.operation, operation);
        assert_eq!(stopped.error, "OAuth writer fenced");
        assert_eq!(snapshot(), before);
        if phase == "fenced" {
            assert_no_resend(
                &fixture.effect,
                &decoded.outcome.commit,
                "late-fenced-retry",
            );
            assert_eq!(snapshot(), before);
            return;
        }
    }

    if phase == "staged" {
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
    let round = phase.strip_suffix("-overlap").unwrap_or(&phase);
    let markers = root.join(round);
    let ready = markers.join("ready");
    let boundary = markers.join("boundary");
    let contending = markers.join("contending");

    if matches!(phase.as_str(), "staged" | "durable") {
        let crash_at = if phase == "staged" {
            CheckpointStage::Staged
        } else {
            CheckpointStage::Durable
        };
        wait_for_marker(&ready);
        let report = receiver.migrate_legacy_oauth_batch_at(
            &oauth,
            [conflict, original(), original()],
            &trusted,
            |item, stage| {
                assert_eq!(item, &operation);
                if stage == crash_at {
                    std::fs::write(&boundary, []).unwrap();
                    std::thread::sleep(Duration::from_secs(10));
                    panic!("parent did not kill worker at {phase} boundary");
                }
                Ok(())
            },
        );
        panic!("worker returned from {phase} batch: {report:?}");
    }

    if phase.ends_with("-overlap") {
        std::fs::write(ready, []).unwrap();
        wait_for_marker(&boundary);
        assert_locked(&oauth_path);
        assert_locked(&pin);
        std::fs::write(contending, []).unwrap();
    }
    if phase == "staged-overlap" {
        let withheld = evidence(&empty, &[]);
        let report = receiver.migrate_legacy_oauth_batch_at(
            &oauth,
            [conflict, withheld, missing],
            &trusted,
            |_, _| panic!("staged image or missing evidence authorized a migration"),
        );
        assert!(report.confirmed.is_empty() && report.stopped.is_none());
        assert_eq!(
            report.pending,
            [operation.clone(), operation.clone(), missing_operation]
        );
        assert_eq!(
            oauth.effect_status(&operation).unwrap(),
            EffectStatus::Unresolved
        );
        assert_eq!(snapshot(), before);
        return;
    }
    if phase.starts_with("peer-") {
        let prefix_operation = OperationId(fixture.prefix.operation.clone());
        let prefix = receiver.evidence(&prefix_operation).unwrap().unwrap();
        let first = DurableEffectRecovery {
            effect: &fixture.prefix,
            ..evidence(&prefix.journal, std::slice::from_ref(&prefix.outcome))
        };
        let batch = [first, missing, conflict, original()]
            .into_iter()
            .enumerate()
            .map(|(index, item)| {
                if index == 3 {
                    std::fs::write(root.join("peer-between-items"), []).unwrap();
                    wait_for_marker(&root.join("resume-items"));
                }
                item
            });
        let report = receiver.migrate_legacy_oauth_batch_at(&oauth, batch, &trusted, |_, _| {
            panic!("overlapping batch attempted a migration write");
        });
        assert_eq!(report.confirmed, [prefix_operation]);
        assert_eq!(report.pending, [missing_operation, operation.clone()]);
        let stopped = report.stopped.unwrap();
        assert_eq!(stopped.operation, operation);
        assert_eq!(stopped.error, "OAuth writer fenced");
        return;
    }
    if matches!(phase.as_str(), "takeover-first" | "durable-overlap") {
        let prefix_operation = OperationId(fixture.prefix.operation.clone());
        let prefix = if phase == "takeover-first" {
            Some(receiver.evidence(&prefix_operation).unwrap().unwrap())
        } else {
            None
        };
        let (first, second, confirmed, stopped) = match &prefix {
            Some(prefix) => (
                DurableEffectRecovery {
                    effect: &fixture.prefix,
                    ..evidence(&prefix.journal, std::slice::from_ref(&prefix.outcome))
                },
                original(),
                prefix_operation,
                operation,
            ),
            None => (original(), missing, operation, missing_operation),
        };
        let batch = [first, second]
            .into_iter()
            .enumerate()
            .map(|(index, item)| {
                if index == 1 {
                    std::fs::write(root.join("between-items"), []).unwrap();
                    wait_for_marker(&root.join("resume-items"));
                }
                item
            });
        let report = receiver.migrate_legacy_oauth_batch_at(&oauth, batch, &trusted, |_, _| {
            panic!("interrupted batch attempted a migration write");
        });
        assert_eq!(report.confirmed, [confirmed]);
        assert!(report.pending.is_empty());
        let failure = report.stopped.unwrap();
        assert_eq!(failure.operation, stopped);
        assert_eq!(failure.error, "OAuth writer fenced");
        return;
    }
    if phase == "rebind" {
        let mut durable = false;
        let report = receiver.migrate_legacy_oauth_batch_at(
            &oauth,
            [conflict, original(), missing],
            &trusted,
            |item, stage| {
                assert_eq!(item, &operation);
                if stage == CheckpointStage::Durable {
                    assert!(!durable);
                    durable = true;
                    return Err("late batch acknowledgment lost".into());
                }
                Ok(())
            },
        );
        assert!(durable);
        assert!(report.confirmed.is_empty());
        assert_eq!(report.pending, std::slice::from_ref(&operation));
        let stopped = report.stopped.unwrap();
        assert_eq!(stopped.operation, operation);
        assert_eq!(stopped.error, "late batch acknowledgment lost");
        assert_eq!(
            oauth.effect_status(&operation).unwrap(),
            EffectStatus::Reconciled
        );
        return;
    }
    assert!(matches!(
        phase.as_str(),
        "resumed-a" | "resumed-b" | "recovered-a" | "recovered-b" | "ack-lost-a" | "ack-lost-b"
    ));
    std::fs::write(signals.join(&phase), []).unwrap();
    let (round, side) = phase.rsplit_once('-').unwrap();
    let other = format!("{round}-{}", if side == "a" { "b" } else { "a" });
    wait_for_marker(&signals.join(other));
    let committed = snapshot();
    let (items, pending) = if phase.ends_with("-b") {
        (
            [missing, original(), original(), conflict],
            [missing_operation.clone(), operation.clone()],
        )
    } else {
        (
            [original(), conflict, missing, original()],
            [operation.clone(), missing_operation.clone()],
        )
    };
    let items = items.into_iter().enumerate().map(|(index, item)| {
        let pause_after = if phase == "resumed-a" { 1 } else { 2 };
        if phase.starts_with("resumed-") && index == pause_after {
            std::fs::write(signals.join(format!("recovery-paused-{phase}")), []).unwrap();
            wait_for_marker(&signals.join("recovery-continue"));
        }
        item
    });
    let report = receiver.migrate_legacy_oauth_batch_at(&oauth, items, &trusted, |_, _| {
        panic!("retry attempted a second migration write")
    });
    if phase.starts_with("resumed-") {
        assert_eq!(phase, fixture.first_worker.other().phase("resumed"));
        assert_eq!(report.confirmed, std::slice::from_ref(&operation));
        let expected_pending = if phase.ends_with("-b") {
            vec![missing_operation.clone()]
        } else {
            Vec::new()
        };
        assert_eq!(report.pending, expected_pending);
        let stopped = report.stopped.unwrap();
        assert_eq!(stopped.operation, operation);
        assert_eq!(stopped.error, "OAuth writer fenced");
        std::fs::write(signals.join("recovery-second-fenced"), []).unwrap();
        wait_for_marker(&signals.join("recovery-second-acknowledgment"));
        panic!("parent did not kill the second recovery worker");
    }
    assert_eq!(report.confirmed, [operation.clone(), operation.clone()]);
    assert_eq!(report.pending, pending);
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

    assert_no_resend(
        &fixture.effect,
        &decoded.outcome.commit,
        "late-reconciled-retry",
    );
    assert_no_resend(
        &fixture.missing,
        &fixture.missing_intent,
        "late-unresolved-retry",
    );
    assert_eq!(snapshot(), committed);
    assert!(receiver.evidence(&missing_operation).unwrap().is_none());
    if phase == fixture.first_worker.phase("ack-lost") {
        std::fs::write(signals.join("confirmation-verified"), []).unwrap();
        wait_for_marker(&signals.join("confirmation-acknowledgment"));
        panic!("parent did not drop the repeated confirmation");
    }
}
