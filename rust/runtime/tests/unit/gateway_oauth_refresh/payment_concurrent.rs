use super::{
    CHILD, Confirmation, DurableRefreshLedger, EffectStatus, Intent, ROOT, ReceiverDelivery,
    ReceiverDispatch, Signed, Snapshot, Stdio, WINDOW, Witness, commerce, digest,
    durable_directory, enroll_for_audience, evidence, oauth_current, payment_simulator, receiver,
    simulation_key, snapshot, verified,
};
use crate::gateway::oauth_refresh_durable::WriterCut;
use crate::gateway::provider::{ProviderAction, ProviderJournal, ProviderRequest};
use crate::gateway::{ProviderOutcome, verify};
use std::path::Path;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

pub(super) const RACE_CHILD: &str =
    "gateway::oauth_refresh::tests::current_commit::payment_crash::concurrent::concurrent_worker";
pub(super) const PHASE: &str = "CEDAR_PAYMENT_RACE_WORKER";

#[derive(serde::Deserialize)]
struct Plan {
    boundary: String,
    order: String,
    snapshots: Vec<Snapshot>,
}

pub(super) fn wait_marker(root: &Path, marker: &str) {
    let start = Instant::now();
    while !root.join(marker).exists() {
        assert!(
            start.elapsed() < Duration::from_secs(10),
            "waiting for {marker}, evidence at {root:?}"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
}

pub(super) fn spawn(root: &Path, test: &str, phase_key: &str, phase: &str) -> Child {
    Command::new(std::env::current_exe().unwrap())
        .args(["--ignored", "--exact", test])
        .env(ROOT, root)
        .env(phase_key, phase)
        .stdout(Stdio::from(
            std::fs::File::create(root.join(format!("{phase}.stdout"))).unwrap(),
        ))
        .stderr(Stdio::from(
            std::fs::File::create(root.join(format!("{phase}.stderr"))).unwrap(),
        ))
        .spawn()
        .unwrap()
}

pub(super) fn finish(mut child: Child, phase: &str, root: &Path) {
    let status = child.wait().unwrap();
    assert!(status.success(), "{phase}: {status}; evidence at {root:?}");
}

#[test]
#[ignore = "spawned by the concurrent payment recovery replay"]
fn concurrent_worker() {
    let root = std::path::PathBuf::from(std::env::var_os(ROOT).unwrap());
    let worker = std::env::var(PHASE).unwrap();
    assert!(worker == "a" || worker == "b");
    let third = root.join("writer3.json").exists();
    let writer_file = if third {
        "writer3.json"
    } else {
        "writer2.json"
    };
    let writer: WriterCut =
        serde_json::from_slice(&std::fs::read(root.join(writer_file)).unwrap()).unwrap();
    let oauth_path = root.join("oauth");
    let ledger = DurableRefreshLedger::new(&oauth_path, "authority").for_writer(writer);
    let receiver_path = root.join(if third { "receiver3" } else { "receiver2" });
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
    let (intent, prepared) = Intent::prepare(&simulator);
    let original = receiver.evidence(&intent.id()).unwrap();
    let absent = ProviderJournal::default();
    let (journal, outcomes): (&ProviderJournal, &[Signed]) = match &original {
        Some(proof) => (&proof.journal, std::slice::from_ref(&proof.outcome)),
        None => (&absent, &[]),
    };
    let facts = intent.audit.facts.accepts(&intent.envelope.facts).unwrap();
    let conflicting_action = ProviderAction {
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
    .sign_outcome(conflicting_action.clone(), &provider)
    .unwrap();
    let decoded: ProviderOutcome = verify(&conflicting, provider.verifying_key()).unwrap();
    assert_eq!(decoded.outcome.action, conflicting_action);
    if let Some(proof) = &original {
        assert_ne!(conflicting, proof.outcome);
    }
    let conflicting_journal = ProviderJournal::observation(conflicting_action);
    std::fs::write(root.join(format!("race-{worker}-ready")), b"ready").unwrap();
    wait_marker(&root, &format!("race-{worker}-go"));
    if worker == "a" {
        assert!(
            !receiver
                .reconcile_oauth(
                    &ledger,
                    evidence(
                        &intent,
                        &provider,
                        &conflicting_journal,
                        std::slice::from_ref(&conflicting)
                    )
                )
                .unwrap()
        );
    } else {
        assert_eq!(
            receiver
                .reconcile_oauth(&ledger, evidence(&intent, &provider, journal, outcomes))
                .unwrap(),
            original.is_some()
        );
    }
    std::fs::write(root.join(format!("race-{worker}-done")), b"done").unwrap();
    wait_marker(&root, "race-repeat-go");
    assert_eq!(
        receiver
            .reconcile_oauth(&ledger, evidence(&intent, &provider, journal, outcomes))
            .unwrap(),
        original.is_some()
    );
    assert!(
        !receiver
            .reconcile_oauth(
                &ledger,
                evidence(
                    &intent,
                    &provider,
                    &conflicting_journal,
                    std::slice::from_ref(&conflicting)
                )
            )
            .unwrap()
    );
    let checked = ledger.checkpoint().unwrap();
    let pin = ledger.effect_checkpoint().unwrap();
    let current = oauth_current(&grant, &format!("race-retry-{worker}"));
    let dispatch = ReceiverDispatch::sign(
        receiver.cut().unwrap(),
        "race-retry",
        &intent.signed,
        &signer,
    )
    .unwrap();
    assert!(
        receiver
            .receive_current_oauth(
                &ledger,
                intent.input(
                    prepared,
                    &current,
                    &checked,
                    &pin,
                    provider.verifying_key(),
                    Some(purchase.use_payment(&host, &steps))
                ),
                ReceiverDelivery {
                    authorization: &dispatch,
                    channel: "race-retry",
                    effect: &intent.envelope.effect,
                    bindings: &facts,
                    facts: &intent.envelope.facts,
                    publications: &[]
                }
            )
            .unwrap()
            .is_none()
    );
    assert!(ledger.recover_effects(&pin).unwrap());
}

#[test]
#[ignore = "requires the Lean-generated concurrent payment plan from just check-gateway"]
fn lean_concurrent_payment_recovery() {
    use std::os::unix::process::ExitStatusExt;
    let file = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/gateway-payment-concurrent-plan.json");
    let plans: Vec<Plan> = serde_json::from_slice(&std::fs::read(file).unwrap()).unwrap();
    assert_eq!(plans.len(), 4);
    for plan in plans {
        let root = durable_directory(&format!("payment-race-{}-{}", plan.boundary, plan.order));
        for dir in [
            "oauth",
            "receiver0",
            "receiver1",
            "receiver2",
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
        let mut winner = spawn(&root, CHILD, WINDOW, &plan.boundary);
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
        let original = third.evidence(&intent.id()).unwrap();
        observed.push(snapshot(
            &root,
            &active2,
            &third,
            &intent.id(),
            writer2.generation(),
            "revoked-handoff",
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
            _ => panic!("unexpected order"),
        };
        std::fs::write(root.join(format!("race-{one}-go")), b"go").unwrap();
        wait_marker(&root, &format!("race-{one}-done"));
        observed.push(snapshot(
            &root,
            &active2,
            &third,
            &intent.id(),
            writer2.generation(),
            "first",
            one,
        ));
        std::fs::write(root.join(format!("race-{two}-go")), b"go").unwrap();
        wait_marker(&root, &format!("race-{two}-done"));
        observed.push(snapshot(
            &root,
            &active2,
            &third,
            &intent.id(),
            writer2.generation(),
            "second",
            two,
        ));
        let before_repeat = active2.effect_checkpoint().unwrap();
        std::fs::write(root.join("race-repeat-go"), b"go").unwrap();
        finish(worker_a, "a", &root);
        finish(worker_b, "b", &root);
        assert!(active2.recover_effects(&before_repeat).unwrap());
        assert_eq!(
            third.evidence(&intent.id()).unwrap().map(|e| e.outcome),
            original.map(|e| e.outcome)
        );
        assert_eq!(
            active2.effect_status(&intent.id()).unwrap(),
            if plan.boundary == "receiver-durable" {
                EffectStatus::Reconciled
            } else {
                EffectStatus::Unresolved
            }
        );
        observed.push(snapshot(
            &root,
            &active2,
            &third,
            &intent.id(),
            writer2.generation(),
            "repeat",
            "both",
        ));
        assert_eq!(
            observed, plan.snapshots,
            "Lean/Rust mismatch for {} {}",
            plan.boundary, plan.order
        );
        eprintln!(
            "PAYMENT-CONCURRENT-TRACE-OK {} {} steps={}",
            plan.boundary,
            plan.order,
            observed.len()
        );
        std::fs::remove_dir_all(root).unwrap();
    }
}
