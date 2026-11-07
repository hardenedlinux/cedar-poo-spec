use super::concurrent::{PHASE, RACE_CHILD, finish, spawn, wait_marker};
use super::{
    CHILD, CheckpointStage, Confirmation, DurableRefreshLedger, EffectStatus, Intent, ROOT, WINDOW,
    Witness, commerce, digest, durable_directory, enroll_for_audience, evidence, payment_simulator,
    receiver, simulation_key, snapshot, verified,
};
use crate::gateway::oauth_refresh_durable::WriterCut;
use crate::gateway::provider::{ProviderAction, ProviderJournal, ProviderRequest};
use crate::gateway::{ProviderOutcome, verify};
use std::path::Path;

const RECRASH_CHILD: &str =
    "gateway::oauth_refresh::tests::current_commit::payment_crash::recrash::recrash_worker";
const RECRASH_PHASE: &str = "CEDAR_PAYMENT_RECRASH_WORKER";

#[derive(serde::Deserialize)]
struct Plan {
    boundary: String,
    order: String,
    snapshots: Vec<super::Snapshot>,
}

#[test]
#[ignore = "spawned by the concurrent reconciliation crash replay"]
fn recrash_worker() {
    let root = std::path::PathBuf::from(std::env::var_os(ROOT).unwrap());
    let worker = std::env::var(RECRASH_PHASE).unwrap();
    assert!(worker == "a" || worker == "b");
    let writer: WriterCut =
        serde_json::from_slice(&std::fs::read(root.join("writer2.json")).unwrap()).unwrap();
    let oauth_path = root.join("oauth");
    let ledger = DurableRefreshLedger::new(&oauth_path, "authority").for_writer(writer);
    let receiver_path = root.join("receiver2");
    let pin_path = root.join("receiver-pin");
    let signer = simulation_key(4);
    let provider = simulation_key(8);
    let witness = Witness::simulation().verifying_key();
    let receiver = receiver(&receiver_path, &pin_path, &signer, &witness, &provider);
    let grant: crate::gateway::oauth::Grant =
        serde_json::from_slice(&std::fs::read(root.join("grant.json")).unwrap()).unwrap();
    let (purchase, host) = commerce();
    let steps = purchase.steps();
    let simulator = payment_simulator(
        "crash-payment",
        &purchase.use_payment(&host, &steps),
        &grant,
    );
    let (intent, _) = Intent::prepare(&simulator);
    let original = receiver.evidence(&intent.id()).unwrap().unwrap();
    let facts = intent.audit.facts.accepts(&intent.envelope.facts).unwrap();
    let action = ProviderAction {
        effect: intent.envelope.effect.clone(),
        result: "conflicting-result".into(),
    };
    let conflicting = ProviderRequest {
        effect: &intent.envelope.effect,
        commit: &intent.signed,
        log_key: &witness,
        bindings: &facts,
        facts: &intent.envelope.facts,
        publications: &[],
    }
    .sign_outcome(action.clone(), &provider)
    .unwrap();
    let decoded: ProviderOutcome = verify(&conflicting, provider.verifying_key()).unwrap();
    assert_eq!(decoded.outcome.action, action);
    assert_ne!(conflicting, original.outcome);
    let journal = ProviderJournal::observation(action);
    std::fs::write(root.join(format!("recrash-{worker}-ready")), b"ready").unwrap();
    if worker == "b" {
        wait_marker(&root, "recrash-b-go");
        let target = match std::fs::read_to_string(root.join("recrash-stage"))
            .unwrap()
            .as_str()
        {
            "staged" => CheckpointStage::Staged,
            "durable" => CheckpointStage::Durable,
            _ => panic!("unknown reconciliation boundary"),
        };
        let result = receiver.reconcile_oauth_at(
            &ledger,
            evidence(
                &intent,
                &provider,
                &original.journal,
                std::slice::from_ref(&original.outcome),
            ),
            None,
            |stage| {
                if stage == target {
                    std::fs::write(root.join("recrash-locked"), b"locked").unwrap();
                    loop {
                        std::thread::park();
                    }
                }
                Ok(())
            },
        );
        panic!("worker B passed requested crash boundary: {result:?}");
    }
    wait_marker(&root, "recrash-locked");
    let lock = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(oauth_path.join("checkpoint.lock"))
        .unwrap();
    assert!(
        matches!(lock.try_lock(), Err(std::fs::TryLockError::WouldBlock)),
        "worker B must hold the OAuth writer lock"
    );
    drop(lock);
    std::fs::write(root.join("recrash-conflict-attempt"), b"contended").unwrap();
    assert!(
        !receiver
            .reconcile_oauth(
                &ledger,
                evidence(
                    &intent,
                    &provider,
                    &journal,
                    std::slice::from_ref(&conflicting)
                )
            )
            .unwrap()
    );
    std::fs::write(root.join("recrash-a-done"), b"done").unwrap();
}

#[test]
#[ignore = "requires the Lean-generated concurrent reconciliation crash plan"]
fn lean_concurrent_payment_recrash() {
    use std::os::unix::process::ExitStatusExt;
    let file = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/gateway-payment-recrash-plan.json");
    let plans: Vec<Plan> = serde_json::from_slice(&std::fs::read(file).unwrap()).unwrap();
    assert_eq!(plans.len(), 4);
    for plan in plans {
        let root = durable_directory(&format!("payment-recrash-{}-{}", plan.boundary, plan.order));
        for dir in [
            "oauth",
            "receiver0",
            "receiver1",
            "receiver2",
            "receiver3",
            "receiver-pin",
        ] {
            std::fs::create_dir(root.join(dir)).unwrap();
        }
        let oauth_path = root.join("oauth");
        let pin_path = root.join("receiver-pin");
        let paths = [
            root.join("receiver0"),
            root.join("receiver1"),
            root.join("receiver2"),
            root.join("receiver3"),
        ];
        let ledger = DurableRefreshLedger::new(&oauth_path, "authority");
        ledger.initialize().unwrap();
        let grant = enroll_for_audience(
            Confirmation::Dpop("key".into()),
            "initial",
            "payments",
            |input| ledger.enroll(input).unwrap(),
        );
        std::fs::write(root.join("grant.json"), serde_json::to_vec(&grant).unwrap()).unwrap();
        let signer = simulation_key(4);
        let provider = simulation_key(8);
        let witness = Witness::simulation().verifying_key();
        let first = receiver(&paths[0], &pin_path, &signer, &witness, &provider);
        first.initialize().unwrap();
        first.bind_oauth(&ledger).unwrap();
        let (purchase, host) = commerce();
        let steps = purchase.steps();
        let simulator = payment_simulator(
            "crash-payment",
            &purchase.use_payment(&host, &steps),
            &grant,
        );
        let (intent, _) = Intent::prepare(&simulator);
        let mut winner = spawn(&root, CHILD, WINDOW, "receiver-durable");
        wait_marker(&root, "crash-ready");
        winner.kill().unwrap();
        assert_eq!(winner.wait().unwrap().signal(), Some(9));
        let mut observed = vec![snapshot(
            &root,
            &ledger,
            &first,
            &intent.id(),
            0,
            "winner-crash",
            "winner",
        )];
        let original = first.evidence(&intent.id()).unwrap().unwrap();
        let initial = ledger.effect_checkpoint().unwrap();
        std::fs::write(
            root.join("writer0.json"),
            serde_json::to_vec(&WriterCut::default()).unwrap(),
        )
        .unwrap();
        let mut pre_a = spawn(&root, CHILD, WINDOW, "preflight-a");
        let mut pre_b = spawn(&root, CHILD, WINDOW, "preflight-b");
        assert_ne!(pre_a.id(), pre_b.id());
        wait_marker(&root, "preflight-a-ready");
        wait_marker(&root, "preflight-b-ready");
        pre_a.kill().unwrap();
        pre_b.kill().unwrap();
        assert_eq!(pre_a.wait().unwrap().signal(), Some(9));
        assert_eq!(pre_b.wait().unwrap().signal(), Some(9));
        assert!(ledger.recover_effects(&initial).unwrap());
        let pin0 = first.acknowledged_checkpoint().unwrap();
        std::fs::copy(
            paths[0].join("checkpoint.json"),
            paths[1].join("checkpoint.json"),
        )
        .unwrap();
        let second = receiver(&paths[1], &pin_path, &signer, &witness, &provider);
        let writer1 = ledger.rotate_writer().unwrap();
        let active1 = ledger.for_writer(writer1);
        second.promote(&pin0).unwrap();
        assert!(ledger.checkpoint().is_err());
        assert!(first.cut().is_err());
        observed.push(snapshot(
            &root,
            &active1,
            &second,
            &intent.id(),
            writer1.generation(),
            "handoff",
            "a",
        ));
        assert!(active1.revoke(verified(digest())).unwrap());
        let pin1 = second.acknowledged_checkpoint().unwrap();
        std::fs::copy(
            paths[1].join("checkpoint.json"),
            paths[2].join("checkpoint.json"),
        )
        .unwrap();
        let third = receiver(&paths[2], &pin_path, &signer, &witness, &provider);
        let writer2 = active1.rotate_writer().unwrap();
        let active2 = ledger.for_writer(writer2);
        third.promote(&pin1).unwrap();
        assert!(active1.checkpoint().is_err());
        assert!(second.cut().is_err());
        std::fs::write(
            root.join("writer2.json"),
            serde_json::to_vec(&writer2).unwrap(),
        )
        .unwrap();
        std::fs::write(root.join("recrash-stage"), plan.boundary.as_bytes()).unwrap();
        observed.push(snapshot(
            &root,
            &active2,
            &third,
            &intent.id(),
            writer2.generation(),
            "revoked-handoff",
            "both",
        ));
        let worker_a = spawn(&root, RECRASH_CHILD, RECRASH_PHASE, "a");
        let mut worker_b = spawn(&root, RECRASH_CHILD, RECRASH_PHASE, "b");
        assert_ne!(worker_a.id(), worker_b.id());
        wait_marker(&root, "recrash-a-ready");
        wait_marker(&root, "recrash-b-ready");
        std::fs::write(root.join("recrash-b-go"), b"go").unwrap();
        wait_marker(&root, "recrash-locked");
        wait_marker(&root, "recrash-conflict-attempt");
        worker_b.kill().unwrap();
        assert_eq!(worker_b.wait().unwrap().signal(), Some(9));
        wait_marker(&root, "recrash-a-done");
        finish(worker_a, "recrash-a", &root);
        assert_eq!(
            active2.effect_status(&intent.id()).unwrap(),
            if plan.boundary == "durable" {
                EffectStatus::Reconciled
            } else {
                EffectStatus::Unresolved
            }
        );
        assert_eq!(
            third.evidence(&intent.id()).unwrap().unwrap().outcome,
            original.outcome
        );
        observed.push(snapshot(
            &root,
            &active2,
            &third,
            &intent.id(),
            writer2.generation(),
            "reconcile-crash",
            "b",
        ));
        let pin2 = third.acknowledged_checkpoint().unwrap();
        std::fs::copy(
            paths[2].join("checkpoint.json"),
            paths[3].join("checkpoint.json"),
        )
        .unwrap();
        let fourth = receiver(&paths[3], &pin_path, &signer, &witness, &provider);
        let writer3 = active2.rotate_writer().unwrap();
        let active3 = ledger.for_writer(writer3);
        fourth.promote(&pin2).unwrap();
        assert!(active2.checkpoint().is_err());
        assert!(third.cut().is_err());
        let stale_evidence = || {
            evidence(
                &intent,
                &provider,
                &original.journal,
                std::slice::from_ref(&original.outcome),
            )
        };
        assert!(
            fourth
                .reconcile_oauth(&active2, stale_evidence())
                .unwrap_err()
                .contains("writer fenced")
        );
        assert!(third.reconcile_oauth(&active3, stale_evidence()).is_err());
        std::fs::write(
            root.join("writer3.json"),
            serde_json::to_vec(&writer3).unwrap(),
        )
        .unwrap();
        observed.push(snapshot(
            &root,
            &active3,
            &fourth,
            &intent.id(),
            writer3.generation(),
            "handoff",
            "both",
        ));
        let worker_a = spawn(&root, RACE_CHILD, PHASE, "a");
        let worker_b = spawn(&root, RACE_CHILD, PHASE, "b");
        assert_ne!(worker_a.id(), worker_b.id());
        wait_marker(&root, "race-a-ready");
        wait_marker(&root, "race-b-ready");
        let (one, two) = match plan.order.as_str() {
            "conflict-first" => ("a", "b"),
            "original-first" => ("b", "a"),
            _ => panic!("unknown order"),
        };
        std::fs::write(root.join(format!("race-{one}-go")), b"go").unwrap();
        wait_marker(&root, &format!("race-{one}-done"));
        observed.push(snapshot(
            &root,
            &active3,
            &fourth,
            &intent.id(),
            writer3.generation(),
            "first",
            one,
        ));
        std::fs::write(root.join(format!("race-{two}-go")), b"go").unwrap();
        wait_marker(&root, &format!("race-{two}-done"));
        observed.push(snapshot(
            &root,
            &active3,
            &fourth,
            &intent.id(),
            writer3.generation(),
            "second",
            two,
        ));
        let before_repeat = active3.effect_checkpoint().unwrap();
        std::fs::write(root.join("race-repeat-go"), b"go").unwrap();
        finish(worker_a, "a", &root);
        finish(worker_b, "b", &root);
        assert!(active3.recover_effects(&before_repeat).unwrap());
        assert_eq!(
            fourth.evidence(&intent.id()).unwrap().unwrap().outcome,
            original.outcome
        );
        assert_eq!(
            active3.effect_status(&intent.id()).unwrap(),
            EffectStatus::Reconciled
        );
        observed.push(snapshot(
            &root,
            &active3,
            &fourth,
            &intent.id(),
            writer3.generation(),
            "repeat",
            "both",
        ));
        assert_eq!(
            observed, plan.snapshots,
            "Lean/Rust mismatch for {} {}",
            plan.boundary, plan.order
        );
        eprintln!(
            "PAYMENT-RECRASH-TRACE-OK {} {} steps={}",
            plan.boundary,
            plan.order,
            observed.len()
        );
        std::fs::remove_dir_all(root).unwrap();
    }
}
