use super::{
    CheckpointStage, CommerceAdmissionHost, Confirmation, DurableEffectRecovery, DurableReceiver,
    DurableRefreshLedger, EffectStatus, Intent, ManagedDeliveryStage, ProviderAuditTrust,
    ReceiverDelivery, ReceiverDispatch, ReceiverTrust, SignedPurchase, Witness, durable_directory,
    enroll_for_audience, oauth_current, payment_simulator, simulation_key,
};

#[test]
fn post_winner_workers_compete_on_current_oauth_and_budget() {
    let path = durable_directory("post-winner-oauth");
    let receiver_path = durable_directory("post-winner-receiver");
    let receiver_pin = durable_directory("post-winner-pin");
    let ledger = DurableRefreshLedger::new(&path, "authority");
    ledger.initialize().unwrap();
    let grant = enroll_for_audience(
        Confirmation::Dpop("key".into()),
        "initial",
        "payments",
        |input| ledger.enroll(input).unwrap(),
    );
    let signer = simulation_key(4);
    let provider = simulation_key(8);
    let witness = Witness::simulation().verifying_key();
    let receiver = DurableReceiver::managed(
        &receiver_path,
        &receiver_pin,
        ReceiverTrust {
            scope: "payments",
            sender: signer.verifying_key(),
            witness: &witness,
            provider: &provider,
        },
    )
    .unwrap();
    receiver.initialize().unwrap();
    receiver.bind_oauth(&ledger).unwrap();
    let principal = simulation_key(1);
    let agent = simulation_key(2);
    let merchant = simulation_key(3);
    let purchases = [
        SignedPurchase::with_amount(&principal, &agent, &merchant, 5, 30),
        SignedPurchase::new(&principal, &agent, &merchant, 6),
        SignedPurchase::new(&principal, &agent, &merchant, 7),
    ];
    let mut host = CommerceAdmissionHost::new();
    host.enroll_principal_key(
        purchases[0].root.principal.clone(),
        *principal.verifying_key(),
    );
    host.enroll_merchant_key(
        purchases[0].offer.merchant_id.clone(),
        *merchant.verifying_key(),
    );
    host.set_policy_epoch(purchases[0].root.principal.clone(), 7)
        .unwrap();
    let steps = purchases.each_ref().map(SignedPurchase::steps);
    for index in 1..=2 {
        assert!(
            host.admit_delegated(
                purchases[index].use_payment(&host, &steps[index]).request,
                |_, _| true
            )
            .is_ok()
        );
        assert!(30 + purchases[index].offer.amount_minor <= purchases[index].root.total_cap);
    }
    let simulators = ["first", "worker-a", "worker-b"]
        .into_iter()
        .enumerate()
        .map(|(i, name)| {
            payment_simulator(name, &purchases[i].use_payment(&host, &steps[i]), &grant)
        })
        .collect::<Vec<_>>();
    let (first, prepared) = Intent::prepare(&simulators[0]);
    let initial_checked = ledger.checkpoint().unwrap();
    let initial_pin = ledger.effect_checkpoint().unwrap();
    let initial_cut = receiver.cut().unwrap();
    let current = oauth_current(&grant, "first-proof");
    let dispatch =
        ReceiverDispatch::sign(initial_cut.clone(), "first", &first.signed, &signer).unwrap();
    let facts = first.audit.facts.accepts(&first.envelope.facts).unwrap();
    let first_result = first
        .input(
            prepared,
            &current,
            &initial_checked,
            &initial_pin,
            provider.verifying_key(),
            Some(purchases[0].use_payment(&host, &steps[0])),
        )
        .mediate(|input, bound| {
            receiver.receive_oauth_at(
                &ledger,
                input,
                ReceiverDelivery {
                    authorization: &dispatch,
                    channel: "first",
                    effect: &first.envelope.effect,
                    bindings: &facts,
                    facts: &first.envelope.facts,
                    publications: &[],
                },
                Some(bound),
                |stage| {
                    if stage == ManagedDeliveryStage::Receiver(CheckpointStage::Durable) {
                        Err("first acknowledgment lost".into())
                    } else {
                        Ok(())
                    }
                },
            )
        });
    assert_eq!(first_result.unwrap_err(), "first acknowledgment lost");
    assert_eq!(
        ledger.effect_status(&first.id()).unwrap(),
        EffectStatus::Unresolved
    );
    let original = receiver.evidence(&first.id()).unwrap().unwrap();
    let checked = ledger.checkpoint().unwrap();
    let pin = ledger.effect_checkpoint().unwrap();
    assert!(!ledger.recover_effects(&initial_pin).unwrap());
    let cut = receiver.cut().unwrap();
    let [(a, a_prepared), (b, b_prepared)] = [
        Intent::prepare(&simulators[1]),
        Intent::prepare(&simulators[2]),
    ];
    let calls = [&a, &b];
    let barrier = std::sync::Barrier::new(2);
    let outcomes = std::thread::scope(|scope| {
        let workers: Vec<_> = [a_prepared, b_prepared]
            .into_iter()
            .enumerate()
            .map(|(index, prepared)| {
                let (
                    ledger,
                    receiver,
                    checked,
                    pin,
                    cut,
                    host,
                    purchases,
                    steps,
                    grant,
                    signer,
                    provider,
                    barrier,
                ) = (
                    &ledger, &receiver, &checked, &pin, &cut, &host, &purchases, &steps, &grant,
                    &signer, &provider, &barrier,
                );
                scope.spawn(move || {
                    let call = calls[index];
                    let current = oauth_current(grant, &format!("post-winner-proof-{index}"));
                    let dispatch =
                        ReceiverDispatch::sign(cut.clone(), "second", &call.signed, signer)
                            .unwrap();
                    let facts = call.audit.facts.accepts(&call.envelope.facts).unwrap();
                    barrier.wait();
                    receiver.receive_current_oauth(
                        ledger,
                        call.input(
                            prepared,
                            &current,
                            checked,
                            pin,
                            provider.verifying_key(),
                            Some(purchases[index + 1].use_payment(host, &steps[index + 1])),
                        ),
                        ReceiverDelivery {
                            authorization: &dispatch,
                            channel: "second",
                            effect: &call.envelope.effect,
                            bindings: &facts,
                            facts: &call.envelope.facts,
                            publications: &[],
                        },
                    )
                })
            })
            .collect();
        workers
            .into_iter()
            .map(|worker| worker.join().unwrap().unwrap())
            .collect::<Vec<_>>()
    });
    assert_eq!(
        outcomes.iter().filter(|outcome| outcome.is_some()).count(),
        1
    );
    let winner = outcomes.iter().position(Option::is_some).unwrap();
    let loser = 1 - winner;
    assert!(receiver.evidence(&calls[winner].id()).unwrap().is_some());
    assert!(receiver.evidence(&calls[loser].id()).unwrap().is_none());
    assert_eq!(
        ledger.effect_status(&calls[loser].id()).unwrap(),
        EffectStatus::Unreserved
    );
    let after_pin = ledger.effect_checkpoint().unwrap();
    assert!(!ledger.recover_effects(&pin).unwrap());
    let image: serde_json::Value =
        serde_json::from_slice(&std::fs::read(path.join("checkpoint.json")).unwrap()).unwrap();
    let effects = image["effects"].as_object().unwrap();
    assert_eq!(effects.len(), 2);
    assert_eq!(
        effects[&first.id().0]["purchase_charge"]["terms"]["amountMinor"],
        30
    );
    assert_eq!(
        effects[&calls[winner].id().0]["purchase_charge"]["terms"]["amountMinor"],
        60
    );
    assert_eq!(
        receiver.evidence(&first.id()).unwrap().unwrap().outcome,
        original.outcome
    );
    // Reload both the OAuth pin and budget after the second winner; 30 + 60 + 60 exceeds the root cap.
    let (retry, prepared) = Intent::prepare(&simulators[loser + 1]);
    let checked = ledger.checkpoint().unwrap();
    let current = oauth_current(&grant, "post-winner-retry-proof");
    let dispatch =
        ReceiverDispatch::sign(receiver.cut().unwrap(), "retry", &retry.signed, &signer).unwrap();
    let facts = retry.audit.facts.accepts(&retry.envelope.facts).unwrap();
    assert!(
        receiver
            .receive_current_oauth(
                &ledger,
                retry.input(
                    prepared,
                    &current,
                    &checked,
                    &after_pin,
                    provider.verifying_key(),
                    Some(purchases[loser + 1].use_payment(&host, &steps[loser + 1]))
                ),
                ReceiverDelivery {
                    authorization: &dispatch,
                    channel: "retry",
                    effect: &retry.envelope.effect,
                    bindings: &facts,
                    facts: &retry.envelope.facts,
                    publications: &[]
                }
            )
            .unwrap()
            .is_none()
    );
    assert!(ledger.recover_effects(&after_pin).unwrap());
    assert_eq!(
        ledger.effect_status(&retry.id()).unwrap(),
        EffectStatus::Unreserved
    );
    assert_eq!(
        receiver.evidence(&first.id()).unwrap().unwrap().outcome,
        original.outcome
    );
    let reconcile = || {
        receiver.reconcile_oauth(
            &ledger,
            DurableEffectRecovery {
                effect: &first.envelope.effect,
                journal: &original.journal,
                outcomes: std::slice::from_ref(&original.outcome),
                history: &first.history,
                trust: ProviderAuditTrust {
                    authority: &first.audit,
                    provider_key: provider.verifying_key(),
                },
            },
        )
    };
    assert!(reconcile().unwrap());
    assert!(reconcile().unwrap());
    assert_eq!(
        ledger.effect_status(&first.id()).unwrap(),
        EffectStatus::Reconciled
    );
    assert_eq!(
        ledger.effect_status(&retry.id()).unwrap(),
        EffectStatus::Unreserved
    );
    for dir in [path, receiver_path, receiver_pin] {
        std::fs::remove_dir_all(dir).unwrap();
    }
}
