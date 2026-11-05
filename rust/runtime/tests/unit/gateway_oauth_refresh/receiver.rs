use super::{
    Confirmation, DurableFinalUse, DurableRefreshLedger, actual, digest, durable_directory,
    enroll_with, verified,
};

#[test]
fn durable_lost_effect_reply_requires_independent_settlement_and_fences_old_writer() {
    use crate::gateway::checkpoint_store::CheckpointStage;
    use crate::gateway::oauth_refresh_durable::{DurableEffectRecovery, DurableEffectUse};
    use crate::gateway::provider_durable::{
        DurableReceiver, ReceiverDelivery, ReceiverDispatch, ReceiverTrust,
    };
    use crate::gateway::wire::{sign, simulation_key};
    use crate::gateway::witness::PrecommitInput;
    use crate::gateway::{
        AuditAuthority, EffectIdentity, FactAuthority, FactBinding, Origin, ProviderAuditTrust,
        ProviderJournal, ReviewBinding, Witness, WitnessFrontier,
    };
    use cedar_poo_core::operation_identity::OperationId;

    let directory = durable_directory("outcome");
    let old = DurableRefreshLedger::new(&directory, "authority");
    old.initialize().unwrap();
    let grant = enroll_with(Confirmation::Dpop("key".into()), |input| {
        old.enroll(input).unwrap()
    });
    let checked = old.checkpoint().unwrap();
    let current = actual(grant.clone(), 14, "first-proof");
    let effect = EffectIdentity {
        operation: "effect".into(),
        object: "object".into(),
        generation: 0,
        payload: "payload".into(),
        action_schema: "schema".into(),
        audience: "fhir".into(),
    };
    let fact = FactBinding {
        issuer: "facts".into(),
        subject: "subject".into(),
        audience: "fhir".into(),
        source: "world".into(),
        field: "field".into(),
        value: "value".into(),
        generation: 0,
        origin: Origin::Observed,
        not_before: 10,
        expires_at: 20,
    };
    let facts = [sign(&fact, &simulation_key(3)).unwrap()];
    let mut review = ReviewBinding {
        before: "policy".into(),
        after: "policy".into(),
        schema: "schema".into(),
        source: "world".into(),
        epoch: 0,
        report: String::new(),
    };
    review.report = crate::json_sha256(&review).unwrap();
    let mut witness = Witness::simulation();
    let intent = witness
        .append(PrecommitInput {
            current_world: "world",
            effect: &effect,
            review: &review,
            facts: std::slice::from_ref(&fact),
            publications: &[],
        })
        .unwrap();
    let fresh = EffectIdentity {
        operation: "unspent-effect".into(),
        ..effect.clone()
    };
    let fresh_intent = witness
        .append(PrecommitInput {
            current_world: "world",
            effect: &fresh,
            review: &review,
            facts: std::slice::from_ref(&fact),
            publications: &[],
        })
        .unwrap();
    let history = witness.snapshot();
    let log_key = witness.verifying_key();
    let provider_signer = simulation_key(8);
    let provider_key = *provider_signer.verifying_key();
    let sender = simulation_key(4);
    let receiver_directory = durable_directory("receiver-outcome");
    let open_receiver = || {
        DurableReceiver::new(
            &receiver_directory,
            ReceiverTrust {
                scope: "receiver",
                sender: sender.verifying_key(),
                witness: &log_key,
                provider: &provider_signer,
            },
        )
    };
    let receiver = open_receiver();
    assert!(receiver.cut().is_err());
    receiver.initialize().unwrap();
    let receiver_cut = receiver.cut().unwrap();
    assert!(
        receiver
            .crash_advance(&receiver_cut, CheckpointStage::Staged)
            .is_err()
    );
    let receiver = open_receiver();
    assert_eq!(receiver.cut().unwrap(), receiver_cut);
    let first_dispatch =
        ReceiverDispatch::sign(receiver_cut.clone(), "channel-one", &intent, &sender).unwrap();
    let deliver = |authorization, channel, effect| ReceiverDelivery {
        authorization,
        channel,
        effect,
        bindings: std::slice::from_ref(&fact),
        facts: &facts,
        publications: &[],
    };
    let audit = AuditAuthority {
        gateway_key: *simulation_key(4).verifying_key(),
        log_key,
        facts: FactAuthority::new(
            vec![fact.clone()],
            [("facts".into(), *simulation_key(3).verifying_key())].into(),
            14,
        )
        .unwrap(),
        minimum_size: 2,
        independent_frontier: Some(
            WitnessFrontier::from_checkpoint(&history.checkpoint, &log_key).unwrap(),
        ),
        review_trust: None,
        prepared_publications: None,
    };
    let trust = ProviderAuditTrust {
        authority: &audit,
        provider_key: &provider_key,
    };
    let use_effect = |checkpoint, current| DurableEffectUse {
        admission: DurableFinalUse {
            checked: checkpoint,
            replica: checkpoint,
            current,
            base_allowed: true,
        },
        effect: &effect,
        intent: &intent,
        history: &history,
        trust,
    };
    assert_eq!(
        old.execute_effect(use_effect(&checked, &current), |actual| {
            assert_eq!(actual, &effect);
            receiver.crash_receive(
                deliver(&first_dispatch, "channel-one", &effect),
                CheckpointStage::Durable,
            )?;
            panic!("receiver should lose the committed reply")
        })
        .unwrap_err(),
        "simulated receiver crash"
    );
    assert!(
        receiver
            .crash_advance(&receiver_cut, CheckpointStage::Durable)
            .is_err()
    );
    let receiver = open_receiver();
    let advanced = receiver.cut().unwrap();
    assert_eq!(advanced.generation, receiver_cut.generation + 1);
    let stale_unspent =
        ReceiverDispatch::sign(receiver_cut, "channel-two", &fresh_intent, &sender).unwrap();
    assert!(
        receiver
            .receive(deliver(&stale_unspent, "channel-two", &fresh))
            .unwrap()
            .is_none()
    );
    let changed_channel =
        ReceiverDispatch::sign(advanced.clone(), "channel-two", &intent, &sender).unwrap();
    assert!(
        receiver
            .receive(deliver(&changed_channel, "channel-two", &effect))
            .unwrap()
            .is_none()
    );
    let retained = receiver
        .evidence(&OperationId(effect.operation.clone()))
        .unwrap()
        .unwrap();
    let provider = retained.journal;
    assert_eq!(provider.actions.len(), 1);

    let cut = old.rotate_writer().unwrap();
    let reopened = DurableRefreshLedger::new(&directory, "authority").for_writer(cut);
    let live = reopened.checkpoint().unwrap();
    let retry = actual(grant, 14, "fresh-proof");
    assert!(old.revoke(verified(digest())).is_err());
    assert!(old.rotate_writer().is_err());
    assert!(
        old.execute_effect(use_effect(&live, &retry), |_| panic!("fenced writer"))
            .is_err()
    );
    assert!(!reopened.recover(&checked).unwrap());
    assert!(
        !reopened
            .execute_effect(use_effect(&live, &retry), |_| panic!("burned effect"))
            .unwrap()
    );
    assert!(reopened.revoke(verified(digest())).unwrap());

    let outcomes = [retained.outcome];
    let evidence = |journal, outcomes| DurableEffectRecovery {
        effect: &effect,
        journal,
        outcomes,
        history: &history,
        trust,
    };
    let absent = ProviderJournal::default();
    let mut forged = outcomes.clone();
    forged[0].signature[0] ^= 1;
    assert!(!reopened.reconcile_effect(evidence(&provider, &[])).unwrap());
    assert!(
        !reopened
            .reconcile_effect(evidence(&provider, &forged))
            .unwrap()
    );
    assert!(
        !reopened
            .reconcile_effect(evidence(&absent, &outcomes))
            .unwrap()
    );
    let alternate = simulation_key(9);
    let decoded: crate::gateway::ProviderOutcome =
        crate::gateway::verify(&outcomes[0], &provider_key).unwrap();
    let substituted = [sign(&decoded, &alternate).unwrap()];
    assert!(
        !reopened
            .reconcile_effect(DurableEffectRecovery {
                trust: ProviderAuditTrust {
                    authority: &audit,
                    provider_key: alternate.verifying_key()
                },
                ..evidence(&provider, &substituted)
            })
            .unwrap()
    );
    assert!(
        reopened
            .reconcile_effect(evidence(&provider, &outcomes))
            .unwrap()
    );
    let reopened = DurableRefreshLedger::new(&directory, "authority").for_writer(cut);
    assert!(
        reopened
            .reconcile_effect(evidence(&provider, &outcomes))
            .unwrap()
    );
    let checkpoint = reopened.checkpoint().unwrap();
    assert!(
        !reopened
            .execute_effect(use_effect(&checkpoint, &retry), |_| panic!(
                "settled effect"
            ))
            .unwrap()
    );
    assert_eq!(provider.actions.len(), 1);
    let fresh_dispatch =
        ReceiverDispatch::sign(advanced, "channel-two", &fresh_intent, &sender).unwrap();
    let fresh_id = OperationId(fresh.operation.clone());
    assert!(
        receiver
            .receive(deliver(&fresh_dispatch, "channel-one", &fresh))
            .unwrap()
            .is_none()
    );
    let mut tampered = fresh_dispatch.clone();
    tampered.signature[0] ^= 1;
    assert!(
        receiver
            .receive(deliver(&tampered, "channel-two", &fresh))
            .is_err()
    );
    assert!(
        receiver
            .crash_receive(
                deliver(&fresh_dispatch, "channel-two", &fresh),
                CheckpointStage::Staged
            )
            .is_err()
    );
    let receiver = open_receiver();
    assert!(receiver.evidence(&fresh_id).unwrap().is_none());
    let delivered = receiver
        .receive(deliver(&fresh_dispatch, "channel-two", &fresh))
        .unwrap()
        .unwrap();
    assert_eq!(
        receiver.evidence(&fresh_id).unwrap().unwrap().outcome,
        delivered
    );
    let failover = durable_directory("receiver-failover");
    let paths: Vec<_> = ["primary", "old", "fork", "interrupted", "standby", "pin"]
        .into_iter()
        .map(|name| {
            let path = failover.join(name);
            std::fs::create_dir(&path).unwrap();
            path
        })
        .collect();
    let [
        primary_path,
        old_path,
        fork_path,
        interrupted_path,
        standby_path,
        pin_path,
    ] = paths.as_slice()
    else {
        unreachable!()
    };
    let config = || ReceiverTrust {
        scope: "failover-receiver",
        sender: sender.verifying_key(),
        witness: &log_key,
        provider: &provider_signer,
    };
    let managed = |path| DurableReceiver::managed(path, pin_path, config()).unwrap();
    let copy = |from: &std::path::Path, to: &std::path::Path| {
        std::fs::copy(from.join("checkpoint.json"), to.join("checkpoint.json")).unwrap();
    };
    let primary = managed(primary_path);
    assert!(managed(standby_path).promote().is_err());
    primary.initialize().unwrap();
    copy(primary_path, old_path);
    let old_cut = primary.cut().unwrap();
    let dispatch =
        ReceiverDispatch::sign(old_cut.clone(), "channel-one", &intent, &sender).unwrap();
    assert!(
        primary
            .crash_receive(
                deliver(&dispatch, "channel-one", &effect),
                CheckpointStage::Durable
            )
            .is_err()
    );
    let operation = OperationId(effect.operation.clone());
    let acknowledged = primary.evidence(&operation).unwrap().unwrap();
    let acknowledged_cut = primary.advance(&old_cut).unwrap();
    assert!(managed(old_path).promote().is_err());

    copy(primary_path, fork_path);
    let mut fork: serde_json::Value =
        serde_json::from_slice(&std::fs::read(fork_path.join("checkpoint.json")).unwrap()).unwrap();
    let old_image: serde_json::Value =
        serde_json::from_slice(&std::fs::read(old_path.join("checkpoint.json")).unwrap()).unwrap();
    assert_ne!(fork["operations"], old_image["operations"]);
    fork["operations"] = old_image["operations"].clone();
    std::fs::write(
        fork_path.join("checkpoint.json"),
        serde_json::to_vec(&fork).unwrap(),
    )
    .unwrap();
    assert!(managed(fork_path).promote().is_err());

    copy(primary_path, interrupted_path);
    copy(primary_path, standby_path);
    assert!(managed(standby_path).cut().is_err());
    assert!(DurableReceiver::new(standby_path, config()).cut().is_err());
    assert!(
        managed(interrupted_path)
            .crash_promote(CheckpointStage::Staged)
            .is_err()
    );
    assert_eq!(primary.cut().unwrap(), acknowledged_cut);
    assert!(managed(interrupted_path).cut().is_err());
    assert!(
        managed(standby_path)
            .crash_promote(CheckpointStage::Durable)
            .is_err()
    );
    let promoted = managed(standby_path);
    let promoted_cut = promoted.cut().unwrap();
    assert_eq!(promoted_cut.generation, acknowledged_cut.generation + 1);
    assert!(primary.cut().is_err());
    // Even an exact copy cannot assume the active placement without promotion.
    copy(standby_path, primary_path);
    assert!(primary.cut().is_err());
    let retired =
        ReceiverDispatch::sign(acknowledged_cut, "channel-two", &fresh_intent, &sender).unwrap();
    assert!(
        promoted
            .receive(deliver(&retired, "channel-two", &fresh))
            .unwrap()
            .is_none()
    );

    let mut reapproval = Witness::simulation();
    let mut reviewed_again = ReviewBinding {
        epoch: review.epoch + 1,
        report: String::new(),
        ..review
    };
    reviewed_again.report = crate::json_sha256(&reviewed_again).unwrap();
    let reapproved = reapproval
        .append(PrecommitInput {
            current_world: "world",
            effect: &effect,
            review: &reviewed_again,
            facts: std::slice::from_ref(&fact),
            publications: &[],
        })
        .unwrap();
    assert_ne!(reapproved, intent);
    let alternate_dispatch =
        ReceiverDispatch::sign(promoted_cut.clone(), "channel-two", &reapproved, &sender).unwrap();
    assert!(
        promoted
            .receive(deliver(&alternate_dispatch, "channel-two", &effect))
            .unwrap()
            .is_none()
    );
    let recovered = promoted.evidence(&operation).unwrap().unwrap();
    assert_eq!(recovered.outcome, acknowledged.outcome);
    assert_eq!(recovered.journal.actions, acknowledged.journal.actions);
    let recovered_outcomes = [recovered.outcome];
    assert!(
        reopened
            .reconcile_effect(evidence(&recovered.journal, &recovered_outcomes))
            .unwrap()
    );
    let permitted =
        ReceiverDispatch::sign(promoted_cut, "channel-two", &fresh_intent, &sender).unwrap();
    assert!(
        primary
            .receive(deliver(&permitted, "channel-two", &fresh))
            .is_err()
    );
    assert!(
        promoted
            .receive(deliver(&permitted, "channel-two", &fresh))
            .unwrap()
            .is_some()
    );
    std::fs::remove_dir_all(failover).unwrap();
    std::fs::remove_dir_all(receiver_directory).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
}
