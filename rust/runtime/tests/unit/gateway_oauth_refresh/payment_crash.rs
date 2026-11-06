use super::{
    CheckpointStage, CommerceAdmissionHost, Confirmation, DurableEffectRecovery, DurableReceiver,
    DurableRefreshLedger, EffectStatus, Intent, ManagedDeliveryStage, OperationId,
    ProviderAuditTrust, ReceiverDelivery, ReceiverDispatch, ReceiverTrust, Signed, SignedPurchase,
    SigningKey, VerifyingKey, Witness, digest, durable_directory, enroll_for_audience,
    oauth_current, payment_simulator, simulation_key, verified,
};
use crate::gateway::wire::sign;
use crate::gateway::{ProviderJournal, ProviderOutcome, verify};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const CHILD: &str =
    "gateway::oauth_refresh::tests::current_commit::payment_crash::payment_crash_worker";
const ROOT: &str = "CEDAR_PAYMENT_CRASH_ROOT";
const WINDOW: &str = "CEDAR_PAYMENT_CRASH_WINDOW";

#[derive(serde::Deserialize)]
struct Plan {
    boundary: String,
    snapshots: Vec<Snapshot>,
}

#[derive(Debug, serde::Deserialize, PartialEq, Eq)]
struct Snapshot {
    writer: u64,
    cut: u64,
    charge: u64,
    receiver_committed: bool,
    status: String,
}

fn commerce() -> (SignedPurchase, CommerceAdmissionHost) {
    let principal = simulation_key(1);
    let agent = simulation_key(2);
    let merchant = simulation_key(3);
    let purchase = SignedPurchase::new(&principal, &agent, &merchant, 5);
    let mut host = CommerceAdmissionHost::new();
    host.enroll_principal_key(purchase.root.principal.clone(), *principal.verifying_key());
    host.enroll_merchant_key(
        purchase.offer.merchant_id.clone(),
        *merchant.verifying_key(),
    );
    host.set_policy_epoch(purchase.root.principal.clone(), 7)
        .unwrap();
    (purchase, host)
}

fn receiver<'a>(
    directory: &'a Path,
    pin: &Path,
    signer: &'a SigningKey,
    witness: &'a VerifyingKey,
    provider: &'a SigningKey,
) -> DurableReceiver<'a> {
    DurableReceiver::managed(
        directory,
        pin,
        ReceiverTrust {
            scope: "payments",
            sender: signer.verifying_key(),
            witness,
            provider,
        },
    )
    .unwrap()
}

#[test]
#[ignore = "spawned by the Lean-aligned payment crash test"]
fn payment_crash_worker() {
    let root = std::path::PathBuf::from(std::env::var_os(ROOT).unwrap());
    let window = std::env::var(WINDOW).unwrap();
    if window.starts_with("restart-") || window.starts_with("preflight-") {
        return payment_restart_worker(&root, &window);
    }
    let ledger_path = root.join("oauth");
    let receiver_path = root.join("receiver0");
    let pin_path = root.join("receiver-pin");
    let ledger = DurableRefreshLedger::new(&ledger_path, "authority");
    let grant: crate::gateway::oauth::Grant =
        serde_json::from_slice(&std::fs::read(root.join("grant.json")).unwrap()).unwrap();
    let signer = simulation_key(4);
    let provider = simulation_key(8);
    let witness = Witness::simulation().verifying_key();
    let receiver = receiver(&receiver_path, &pin_path, &signer, &witness, &provider);
    let (purchase, host) = commerce();
    let steps = purchase.steps();
    let simulator = payment_simulator(
        "crash-payment",
        &purchase.use_payment(&host, &steps),
        &grant,
    );
    let (intent, prepared) = Intent::prepare(&simulator);
    let current = oauth_current(&grant, "crash-proof");
    let checked = ledger.checkpoint().unwrap();
    let pin = ledger.effect_checkpoint().unwrap();
    let dispatch =
        ReceiverDispatch::sign(receiver.cut().unwrap(), "first", &intent.signed, &signer).unwrap();
    let facts = intent.audit.facts.accepts(&intent.envelope.facts).unwrap();
    let target = match window.as_str() {
        "oauth-reserved" => ManagedDeliveryStage::OAuthReserved,
        "receiver-durable" => ManagedDeliveryStage::Receiver(CheckpointStage::Durable),
        _ => panic!("unknown crash window"),
    };
    let result = intent
        .input(
            prepared,
            &current,
            &checked,
            &pin,
            provider.verifying_key(),
            Some(purchase.use_payment(&host, &steps)),
        )
        .mediate(|input, bound| {
            receiver.receive_oauth_at(
                &ledger,
                input,
                ReceiverDelivery {
                    authorization: &dispatch,
                    channel: "first",
                    effect: &intent.envelope.effect,
                    bindings: &facts,
                    facts: &intent.envelope.facts,
                    publications: &[],
                },
                Some(bound),
                |stage| {
                    if stage == target {
                        std::fs::write(root.join("crash-ready"), window.as_bytes()).unwrap();
                        loop {
                            std::thread::park();
                        }
                    }
                    Ok(())
                },
            )
        });
    panic!("worker passed the requested crash point: {result:?}");
}

fn payment_restart_worker(root: &Path, phase: &str) {
    use crate::gateway::oauth_refresh_durable::WriterCut;
    let (directory, writer_file) = match phase {
        "preflight-a" | "preflight-b" => ("receiver0", "writer0.json"),
        "restart-a" => ("receiver1", "writer1.json"),
        "restart-b" => ("receiver2", "writer2.json"),
        "restart-a-stale" => ("receiver2", "writer1.json"),
        _ => panic!("unknown restart phase"),
    };
    let writer: WriterCut =
        serde_json::from_slice(&std::fs::read(root.join(writer_file)).unwrap()).unwrap();
    let oauth_path = root.join("oauth");
    let ledger = DurableRefreshLedger::new(&oauth_path, "authority").for_writer(writer);
    let receiver_path = root.join(directory);
    let pin = root.join("receiver-pin");
    let signer = simulation_key(4);
    let provider = simulation_key(8);
    let witness = Witness::simulation().verifying_key();
    let receiver = receiver(&receiver_path, &pin, &signer, &witness, &provider);
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
    let original = receiver.evidence(&intent.id()).unwrap();
    if phase.starts_with("preflight-") {
        assert_eq!(
            ledger.effect_status(&intent.id()).unwrap(),
            EffectStatus::Unresolved
        );
        std::fs::write(root.join(format!("{phase}-ready")), b"observed").unwrap();
        loop {
            std::thread::park();
        }
    }
    let absent = ProviderJournal::default();
    let (journal, outcomes) = match &original {
        Some(proof) => (&proof.journal, std::slice::from_ref(&proof.outcome)),
        None => (&absent, &[][..]),
    };
    let marker = root.join(format!("{phase}-ready"));
    let result = receiver.reconcile_oauth_at(
        &ledger,
        evidence(&intent, &provider, journal, outcomes),
        None,
        |stage| {
            if phase == "restart-a" && stage == CheckpointStage::Durable {
                std::fs::write(&marker, b"durable").unwrap();
                loop {
                    std::thread::park();
                }
            }
            Ok(())
        },
    );
    if phase == "restart-a-stale" {
        assert!(result.unwrap_err().contains("writer fenced"));
    } else {
        assert_eq!(result.unwrap(), original.is_some());
    }
    if phase == "restart-a" {
        assert!(
            original.is_none(),
            "committed reconciliation must stop at its durable point"
        );
        std::fs::write(marker, b"missing").unwrap();
        loop {
            std::thread::park();
        }
    }
}

fn snapshot(
    root: &Path,
    ledger: &DurableRefreshLedger<'_>,
    receiver: &DurableReceiver<'_>,
    operation: &OperationId,
    writer: u64,
) -> Snapshot {
    let image: serde_json::Value =
        serde_json::from_slice(&std::fs::read(root.join("oauth/checkpoint.json")).unwrap())
            .unwrap();
    let charge = image["effects"][&operation.0]["purchase_charge"]["terms"]["amountMinor"]
        .as_u64()
        .unwrap();
    let status = match ledger.effect_status(operation).unwrap() {
        EffectStatus::Unreserved => "unreserved",
        EffectStatus::Unresolved => "unresolved",
        EffectStatus::Reconciled => "reconciled",
    };
    Snapshot {
        writer,
        cut: receiver.cut().unwrap().generation,
        charge,
        receiver_committed: receiver.evidence(operation).unwrap().is_some(),
        status: status.into(),
    }
}

fn evidence<'a>(
    intent: &'a Intent<'_>,
    provider: &'a SigningKey,
    journal: &'a ProviderJournal,
    outcomes: &'a [Signed],
) -> DurableEffectRecovery<'a> {
    DurableEffectRecovery {
        effect: &intent.envelope.effect,
        journal,
        outcomes,
        history: &intent.history,
        trust: ProviderAuditTrust {
            authority: &intent.audit,
            provider_key: provider.verifying_key(),
        },
    }
}

#[test]
#[ignore = "requires the Lean-generated payment crash plan from just check-gateway"]
fn lean_payment_crash_windows() {
    let file = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/gateway-payment-crash-plan.json");
    let plans: Vec<Plan> = serde_json::from_slice(&std::fs::read(file).unwrap()).unwrap();
    assert_eq!(plans.len(), 2);
    for plan in plans {
        let root = durable_directory(&format!("payment-crash-{}", plan.boundary));
        for dir in [
            "oauth",
            "receiver0",
            "receiver1",
            "receiver2",
            "receiver-pin",
        ] {
            std::fs::create_dir(root.join(dir)).unwrap();
        }
        let ledger_path = root.join("oauth");
        let pin_path = root.join("receiver-pin");
        let initial_path = root.join("receiver0");
        let first_path = root.join("receiver1");
        let second_path = root.join("receiver2");
        let ledger = DurableRefreshLedger::new(&ledger_path, "authority");
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
        let first = receiver(&initial_path, &pin_path, &signer, &witness, &provider);
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
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args(["--ignored", "--exact", CHILD])
            .env(ROOT, &root)
            .env(WINDOW, &plan.boundary)
            .stdout(Stdio::from(
                std::fs::File::create(root.join("worker.stdout")).unwrap(),
            ))
            .stderr(Stdio::from(
                std::fs::File::create(root.join("worker.stderr")).unwrap(),
            ))
            .spawn()
            .unwrap();
        let started = Instant::now();
        while !root.join("crash-ready").exists() {
            if let Some(status) = child.try_wait().unwrap() {
                panic!("worker exited before crash point: {status}, evidence at {root:?}");
            }
            if started.elapsed() >= Duration::from_secs(10) {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("worker did not reach crash point, evidence at {root:?}");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        child.kill().unwrap();
        let killed = child.wait().unwrap();
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(killed.signal(), Some(9));
        // The snapshots compare the protected stores with Lean's finite trace.
        let mut observed = vec![snapshot(&root, &ledger, &first, &intent.id(), 0)];
        let original = first.evidence(&intent.id()).unwrap();
        let before_restart = ledger.effect_checkpoint().unwrap();
        let initial_writer = crate::gateway::oauth_refresh_durable::WriterCut::default();
        std::fs::write(
            root.join("writer0.json"),
            serde_json::to_vec(&initial_writer).unwrap(),
        )
        .unwrap();
        let mut workers: Vec<_> = ["preflight-a", "preflight-b"]
            .into_iter()
            .map(|phase| {
                Command::new(std::env::current_exe().unwrap())
                    .args(["--ignored", "--exact", CHILD])
                    .env(ROOT, &root)
                    .env(WINDOW, phase)
                    .stdout(Stdio::from(
                        std::fs::File::create(root.join(format!("{phase}.stdout"))).unwrap(),
                    ))
                    .stderr(Stdio::from(
                        std::fs::File::create(root.join(format!("{phase}.stderr"))).unwrap(),
                    ))
                    .spawn()
                    .unwrap()
            })
            .collect();
        assert_ne!(workers[0].id(), workers[1].id());
        let started = Instant::now();
        while !["preflight-a-ready", "preflight-b-ready"]
            .iter()
            .all(|name| root.join(name).exists())
        {
            for worker in &mut workers {
                if let Some(status) = worker.try_wait().unwrap() {
                    panic!(
                        "worker exited before restart preparation: {status}, evidence at {root:?}"
                    );
                }
            }
            if started.elapsed() >= Duration::from_secs(10) {
                for worker in &mut workers {
                    worker.kill().unwrap();
                    worker.wait().unwrap();
                }
                panic!("workers did not reach restart preparation, evidence at {root:?}");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        for worker in &mut workers {
            worker.kill().unwrap();
            assert_eq!(worker.wait().unwrap().signal(), Some(9));
        }
        assert!(ledger.recover_effects(&before_restart).unwrap());
        observed.push(snapshot(&root, &ledger, &first, &intent.id(), 0));
        let pin0 = first.acknowledged_checkpoint().unwrap();
        std::fs::copy(
            initial_path.join("checkpoint.json"),
            first_path.join("checkpoint.json"),
        )
        .unwrap();
        let second = receiver(&first_path, &pin_path, &signer, &witness, &provider);
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
        ));
        std::fs::write(
            root.join("writer1.json"),
            serde_json::to_vec(&writer1).unwrap(),
        )
        .unwrap();
        let mut restarted_a = Command::new(std::env::current_exe().unwrap())
            .args(["--ignored", "--exact", CHILD])
            .env(ROOT, &root)
            .env(WINDOW, "restart-a")
            .stdout(Stdio::from(
                std::fs::File::create(root.join("restart-a.stdout")).unwrap(),
            ))
            .stderr(Stdio::from(
                std::fs::File::create(root.join("restart-a.stderr")).unwrap(),
            ))
            .spawn()
            .unwrap();
        let started = Instant::now();
        while !root.join("restart-a-ready").exists() {
            if let Some(status) = restarted_a.try_wait().unwrap() {
                panic!(
                    "worker A exited before reconciliation point: {status}, evidence at {root:?}"
                );
            }
            if started.elapsed() >= Duration::from_secs(10) {
                restarted_a.kill().unwrap();
                restarted_a.wait().unwrap();
                panic!("worker A did not reach reconciliation point, evidence at {root:?}");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        restarted_a.kill().unwrap();
        assert_eq!(restarted_a.wait().unwrap().signal(), Some(9));
        observed.push(snapshot(
            &root,
            &active1,
            &second,
            &intent.id(),
            writer1.generation(),
        ));
        assert!(active1.revoke(verified(digest())).unwrap());
        let pin1 = second.acknowledged_checkpoint().unwrap();
        std::fs::copy(
            first_path.join("checkpoint.json"),
            second_path.join("checkpoint.json"),
        )
        .unwrap();
        let third = receiver(&second_path, &pin_path, &signer, &witness, &provider);
        let writer2 = active1.rotate_writer().unwrap();
        let active2 = ledger.for_writer(writer2);
        third.promote(&pin1).unwrap();
        std::fs::write(
            root.join("writer2.json"),
            serde_json::to_vec(&writer2).unwrap(),
        )
        .unwrap();
        assert!(active1.checkpoint().is_err());
        assert!(second.cut().is_err());
        observed.push(snapshot(
            &root,
            &active2,
            &third,
            &intent.id(),
            writer2.generation(),
        ));
        for phase in ["restart-b", "restart-a-stale"] {
            let output = Command::new(std::env::current_exe().unwrap())
                .args(["--ignored", "--exact", CHILD])
                .env(ROOT, &root)
                .env(WINDOW, phase)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{phase} failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            observed.push(snapshot(
                &root,
                &active2,
                &third,
                &intent.id(),
                writer2.generation(),
            ));
        }
        let checked = active2.checkpoint().unwrap();
        let pin = active2.effect_checkpoint().unwrap();
        let current = oauth_current(&grant, "retry-after-revocation");
        let prepared = simulator.prepare(&intent.envelope).unwrap();
        let dispatch =
            ReceiverDispatch::sign(third.cut().unwrap(), "retry", &intent.signed, &signer).unwrap();
        let facts = intent.audit.facts.accepts(&intent.envelope.facts).unwrap();
        assert!(
            third
                .receive_current_oauth(
                    &active2,
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
                        channel: "retry",
                        effect: &intent.envelope.effect,
                        bindings: &facts,
                        facts: &intent.envelope.facts,
                        publications: &[]
                    }
                )
                .unwrap()
                .is_none()
        );
        let stale_prepared = simulator.prepare(&intent.envelope).unwrap();
        let stale_result = third.receive_current_oauth(
            &ledger,
            intent.input(
                stale_prepared,
                &current,
                &checked,
                &pin,
                provider.verifying_key(),
                Some(purchase.use_payment(&host, &steps)),
            ),
            ReceiverDelivery {
                authorization: &dispatch,
                channel: "retry",
                effect: &intent.envelope.effect,
                bindings: &facts,
                facts: &intent.envelope.facts,
                publications: &[],
            },
        );
        assert!(stale_result.unwrap_err().contains("writer fenced"));
        let absent = ProviderJournal::default();
        assert!(
            !third
                .reconcile_oauth(&active2, evidence(&intent, &provider, &absent, &[]))
                .unwrap()
        );
        if let Some(original) = original {
            let current = third.evidence(&intent.id()).unwrap().unwrap();
            assert_eq!(original.outcome.payload, current.outcome.payload);
            assert_eq!(original.outcome.signature, current.outcome.signature);
            let mut conflict: ProviderOutcome =
                verify(&original.outcome, provider.verifying_key()).unwrap();
            conflict.outcome.action.result = "conflicting-result".into();
            let conflicting = sign(&conflict, &provider).unwrap();
            let journal = ProviderJournal::observation(conflict.outcome.action);
            assert!(
                !third
                    .reconcile_oauth(
                        &active2,
                        evidence(
                            &intent,
                            &provider,
                            &journal,
                            std::slice::from_ref(&conflicting)
                        )
                    )
                    .unwrap()
            );
            for _ in 0..2 {
                assert!(
                    third
                        .reconcile_oauth(
                            &active2,
                            evidence(
                                &intent,
                                &provider,
                                &current.journal,
                                std::slice::from_ref(&current.outcome)
                            )
                        )
                        .unwrap()
                );
            }
            assert!(
                !third
                    .reconcile_oauth(
                        &active2,
                        evidence(
                            &intent,
                            &provider,
                            &journal,
                            std::slice::from_ref(&conflicting)
                        )
                    )
                    .unwrap()
            );
        }
        observed.push(snapshot(
            &root,
            &active2,
            &third,
            &intent.id(),
            writer2.generation(),
        ));
        assert_eq!(
            observed, plan.snapshots,
            "Lean/Rust mismatch for {}",
            plan.boundary
        );
        eprintln!(
            "PAYMENT-CRASH-TRACE-OK {} steps={}",
            plan.boundary,
            observed.len()
        );
        std::fs::remove_dir_all(root).unwrap();
    }
}
