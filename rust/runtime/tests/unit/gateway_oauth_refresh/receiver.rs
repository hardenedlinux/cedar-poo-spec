use super::{
    Confirmation, DurableFinalUse, DurableRefreshLedger, actual, digest, durable_directory,
    enroll_with, verified,
};

#[test]
fn durable_lost_effect_reply_requires_independent_settlement_and_fences_old_writer() {
    use crate::gateway::checkpoint_store::CheckpointStage;
    use crate::gateway::oauth_refresh_durable::{
        DurableEffectRecovery, DurableEffectUse, EffectStatus,
    };
    use crate::gateway::provider_durable::{
        DurableReceiver, ManagedDeliveryStage, ReceiverDelivery, ReceiverDispatch, ReceiverTrust,
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
    let uncertain = EffectIdentity {
        operation: "reserved-without-receipt".into(),
        ..effect.clone()
    };
    let uncertain_intent = witness
        .append(PrecommitInput {
            current_world: "world",
            effect: &uncertain,
            review: &review,
            facts: std::slice::from_ref(&fact),
            publications: &[],
        })
        .unwrap();
    let uncertain_id = OperationId(uncertain.operation.clone());
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
    let paths: Vec<_> = [
        "primary",
        "old",
        "fork",
        "interrupted",
        "standby",
        "peer",
        "lost-reply",
        "pin",
    ]
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
        peer_path,
        lost_reply_path,
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
    let oauth_directory = durable_directory("receiver-oauth");
    let oauth = DurableRefreshLedger::new(&oauth_directory, "receiver-oauth");
    oauth.initialize().unwrap();
    let live_grant = enroll_with(Confirmation::Dpop("key".into()), |input| {
        oauth.enroll(input).unwrap()
    });
    let live_use = actual(live_grant.clone(), 14, "receiver-first-proof");
    let live_checkpoint = oauth.checkpoint().unwrap();
    let primary = managed(primary_path);
    assert!(managed(standby_path).acknowledged_checkpoint().is_err());
    primary.initialize().unwrap();
    primary.bind_oauth(&oauth).unwrap();
    copy(primary_path, old_path);
    let old_cut = primary.cut().unwrap();
    let dispatch =
        ReceiverDispatch::sign(old_cut.clone(), "channel-one", &intent, &sender).unwrap();
    assert!(
        primary
            .receive(deliver(&dispatch, "channel-one", &effect))
            .is_err()
    );
    assert_eq!(
        primary
            .crash_receive_oauth(
                &oauth,
                use_effect(&live_checkpoint, &live_use),
                deliver(&dispatch, "channel-one", &effect),
                ManagedDeliveryStage::Receiver(CheckpointStage::Durable),
            )
            .unwrap_err(),
        "simulated managed delivery crash"
    );
    let operation = OperationId(effect.operation.clone());
    let acknowledged = primary.evidence(&operation).unwrap().unwrap();
    assert_eq!(
        oauth.effect_status(&operation).unwrap(),
        EffectStatus::Unresolved
    );
    assert_eq!(
        oauth.effect_status(&uncertain_id).unwrap(),
        EffectStatus::Unreserved
    );
    let before_reservation = primary.acknowledged_checkpoint().unwrap();
    let uncertain_dispatch =
        ReceiverDispatch::sign(old_cut.clone(), "channel-one", &uncertain_intent, &sender).unwrap();
    let uncertain_use = actual(live_grant.clone(), 14, "reserved-without-receipt-proof");
    assert_eq!(
        primary
            .crash_receive_oauth(
                &oauth,
                DurableEffectUse {
                    admission: DurableFinalUse {
                        checked: &live_checkpoint,
                        replica: &live_checkpoint,
                        current: &uncertain_use,
                        base_allowed: true,
                    },
                    effect: &uncertain,
                    intent: &uncertain_intent,
                    history: &history,
                    trust,
                },
                deliver(&uncertain_dispatch, "channel-one", &uncertain),
                ManagedDeliveryStage::OAuthReserved,
            )
            .unwrap_err(),
        "simulated managed delivery crash"
    );
    let primary = managed(primary_path);
    assert_eq!(
        primary.acknowledged_checkpoint().unwrap(),
        before_reservation
    );
    assert!(primary.evidence(&uncertain_id).unwrap().is_none());
    assert_eq!(
        oauth.effect_status(&uncertain_id).unwrap(),
        EffectStatus::Unresolved
    );
    assert!(
        !oauth
            .execute_final(
                DurableFinalUse {
                    checked: &live_checkpoint,
                    replica: &live_checkpoint,
                    current: &uncertain_use,
                    base_allowed: true,
                },
                || panic!("persisted proof reservation was lost"),
            )
            .unwrap()
    );
    let acknowledged_cut = primary.advance(&old_cut).unwrap();
    let expected = primary.acknowledged_checkpoint().unwrap();
    assert!(managed(old_path).promote(&expected).is_err());

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
    assert!(managed(fork_path).promote(&expected).is_err());

    copy(primary_path, interrupted_path);
    copy(primary_path, standby_path);
    copy(primary_path, peer_path);
    assert!(managed(standby_path).cut().is_err());
    assert!(DurableReceiver::new(standby_path, config()).cut().is_err());
    assert!(
        managed(interrupted_path)
            .crash_promote(&expected, CheckpointStage::Staged)
            .is_err()
    );
    assert_eq!(primary.cut().unwrap(), acknowledged_cut);
    assert!(managed(interrupted_path).cut().is_err());
    let standby = managed(standby_path);
    let peer = managed(peer_path);
    let unavailable = primary_path.join("offline-image");
    std::fs::rename(primary_path.join("checkpoint.json"), &unavailable).unwrap();
    assert!(primary.cut().is_err());
    let race_checkpoint = standby.acknowledged_checkpoint().unwrap();
    assert_eq!(race_checkpoint, expected);
    let start = std::sync::Barrier::new(2);
    let (left, right) = std::thread::scope(|scope| {
        let left = scope.spawn(|| {
            start.wait();
            standby.promote(&race_checkpoint)
        });
        start.wait();
        let right = peer.promote(&race_checkpoint);
        (left.join().unwrap(), right)
    });
    let (winner_path, loser_path, winning_cut) = match (left, right) {
        (Ok(cut), Err(_)) => (standby_path, peer_path, cut),
        (Err(_), Ok(cut)) => (peer_path, standby_path, cut),
        result => panic!("expected exactly one promotion, got {result:?}"),
    };
    let winner = managed(winner_path);
    assert_eq!(winning_cut.generation, acknowledged_cut.generation + 1);
    assert_eq!(
        winner.recover_promotion(&expected).unwrap(),
        Some(winning_cut)
    );
    assert!(managed(loser_path).recover_promotion(&expected).is_err());
    assert!(primary.cut().is_err());

    // The interrupted candidate can hold the same successor image as the
    // winner. Its original promotion must still fail against the new pin.
    assert_eq!(
        std::fs::read(interrupted_path.join("checkpoint.json")).unwrap(),
        std::fs::read(winner_path.join("checkpoint.json")).unwrap()
    );
    assert!(managed(interrupted_path).promote(&expected).is_err());

    let first_writer = oauth.rotate_writer().unwrap();
    let switched = oauth.for_writer(first_writer);
    let current_checkpoint = switched.checkpoint().unwrap();
    let fresh_use = actual(live_grant.clone(), 14, "receiver-unused-proof");
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
        ReceiverDispatch::sign(winner.cut().unwrap(), "channel-two", &reapproved, &sender).unwrap();
    let uncertain_reapproved = reapproval
        .append(PrecommitInput {
            current_world: "world",
            effect: &uncertain,
            review: &reviewed_again,
            facts: std::slice::from_ref(&fact),
            publications: &[],
        })
        .unwrap();
    assert_ne!(uncertain_reapproved, uncertain_intent);
    let alternate_history = reapproval.snapshot();
    let alternate_audit = AuditAuthority {
        gateway_key: audit.gateway_key,
        log_key,
        facts: audit.facts.clone(),
        minimum_size: 1,
        independent_frontier: Some(
            WitnessFrontier::from_checkpoint(&alternate_history.checkpoint, &log_key).unwrap(),
        ),
        review_trust: None,
        prepared_publications: None,
    };
    let alternate_use = |checkpoint| DurableEffectUse {
        admission: DurableFinalUse {
            checked: checkpoint,
            replica: checkpoint,
            current: &fresh_use,
            base_allowed: true,
        },
        intent: &reapproved,
        history: &alternate_history,
        trust: ProviderAuditTrust {
            authority: &alternate_audit,
            provider_key: &provider_key,
        },
        effect: &effect,
    };
    assert!(
        winner
            .receive_oauth(
                &switched,
                alternate_use(&current_checkpoint),
                deliver(&alternate_dispatch, "channel-two", &effect)
            )
            .unwrap()
            .is_none()
    );

    let unknown_reconciliation = || DurableEffectRecovery {
        effect: &uncertain,
        journal: &absent,
        outcomes: &[],
        history: &history,
        trust,
    };
    let retry_uncertain =
        |receiver: &DurableReceiver<'_>, authority: &DurableRefreshLedger<'_>, checkpoint| {
            let dispatch = ReceiverDispatch::sign(
                receiver.cut().unwrap(),
                "channel-three",
                &uncertain_reapproved,
                &sender,
            )
            .unwrap();
            receiver.receive_oauth(
                authority,
                DurableEffectUse {
                    admission: DurableFinalUse {
                        checked: checkpoint,
                        replica: checkpoint,
                        current: &fresh_use,
                        base_allowed: true,
                    },
                    effect: &uncertain,
                    intent: &uncertain_reapproved,
                    history: &alternate_history,
                    trust: ProviderAuditTrust {
                        authority: &alternate_audit,
                        provider_key: &provider_key,
                    },
                },
                ReceiverDelivery {
                    authorization: &dispatch,
                    ..deliver(&uncertain_dispatch, "channel-three", &uncertain)
                },
            )
        };
    assert!(
        !winner
            .reconcile_oauth(&switched, unknown_reconciliation())
            .unwrap()
    );
    assert!(
        retry_uncertain(&winner, &switched, &current_checkpoint)
            .unwrap()
            .is_none()
    );
    assert!(winner.evidence(&uncertain_id).unwrap().is_none());
    assert_eq!(
        switched.effect_status(&uncertain_id).unwrap(),
        EffectStatus::Unresolved
    );

    copy(winner_path, lost_reply_path);
    let committed = winner.acknowledged_checkpoint().unwrap();
    let last_replica = managed(lost_reply_path);
    let fresh_effect = |checkpoint| DurableEffectUse {
        admission: DurableFinalUse {
            checked: checkpoint,
            replica: checkpoint,
            current: &fresh_use,
            base_allowed: true,
        },
        effect: &fresh,
        intent: &fresh_intent,
        history: &history,
        trust,
    };
    let anticipated_cut = cedar_poo_core::operation_identity::ReceiverCut {
        generation: winner.cut().unwrap().generation + 1,
        ..winner.cut().unwrap()
    };
    let takeover_dispatch = ReceiverDispatch::sign(
        anticipated_cut.clone(),
        "channel-two",
        &fresh_intent,
        &sender,
    )
    .unwrap();
    std::thread::scope(|scope| {
        let (committed_revoke, revoke_is_durable) = std::sync::mpsc::channel();
        let (release_revoke, allow_return) = std::sync::mpsc::channel();
        let authority = &switched;
        let revoke = scope.spawn(move || {
            authority.revoke_observed(verified(digest()), |stage| {
                if stage == CheckpointStage::Durable {
                    committed_revoke.send(()).unwrap();
                    allow_return.recv().map_err(|error| error.to_string())?;
                    return Err("simulated checkpoint crash".into());
                }
                Ok(())
            })
        });
        revoke_is_durable.recv().unwrap();
        assert_eq!(
            last_replica
                .crash_promote(&committed, CheckpointStage::Durable)
                .unwrap_err(),
            "simulated receiver crash"
        );
        assert_eq!(last_replica.cut().unwrap(), anticipated_cut);
        let (starting, request_started) = std::sync::mpsc::channel();
        let delivery = deliver(&takeover_dispatch, "channel-two", &fresh);
        let input = fresh_effect(&current_checkpoint);
        let active = &last_replica;
        let attempt = scope.spawn(move || {
            starting.send(()).unwrap();
            active.receive_oauth(authority, input, delivery)
        });
        request_started.recv().unwrap();
        release_revoke.send(()).unwrap();
        assert_eq!(
            revoke.join().unwrap().unwrap_err(),
            "simulated checkpoint crash"
        );
        assert!(attempt.join().unwrap().unwrap().is_none());
    });
    let promoted = managed(lost_reply_path);
    let promoted_cut = promoted.cut().unwrap();
    assert_eq!(promoted_cut.generation, acknowledged_cut.generation + 2);
    assert_eq!(
        promoted.recover_promotion(&committed).unwrap(),
        Some(promoted_cut.clone())
    );
    assert!(promoted.recover_promotion(&expected).unwrap().is_none());
    assert!(winner.recover_promotion(&committed).is_err());
    assert!(managed(loser_path).cut().is_err());
    // Even an exact copy cannot assume the active placement without promotion.
    copy(lost_reply_path, primary_path);
    let primary = managed(primary_path);
    assert!(primary.cut().is_err());
    let next_writer = switched.rotate_writer().unwrap();
    let worker =
        DurableRefreshLedger::new(&oauth_directory, "receiver-oauth").for_writer(next_writer);
    let revoked = worker.checkpoint().unwrap();
    let permitted =
        ReceiverDispatch::sign(promoted_cut.clone(), "channel-two", &fresh_intent, &sender)
            .unwrap();
    assert!(
        promoted
            .receive_oauth(
                &oauth,
                fresh_effect(&live_checkpoint),
                deliver(&permitted, "channel-two", &fresh)
            )
            .is_err()
    );
    for frontier in [&live_checkpoint, &revoked] {
        assert!(
            promoted
                .receive_oauth(
                    &worker,
                    fresh_effect(frontier),
                    deliver(&permitted, "channel-two", &fresh)
                )
                .unwrap()
                .is_none()
        );
    }
    assert!(promoted.evidence(&fresh_id).unwrap().is_none());
    assert!(
        primary
            .receive(deliver(&permitted, "channel-two", &fresh))
            .is_err()
    );
    assert!(
        promoted
            .receive(deliver(&permitted, "channel-two", &fresh))
            .is_err()
    );

    let other_directory = durable_directory("receiver-unbound-oauth");
    let other = DurableRefreshLedger::new(&other_directory, "receiver-oauth");
    other.initialize().unwrap();
    enroll_with(Confirmation::Dpop("key".into()), |input| {
        other.enroll(input).unwrap()
    });
    let other_checkpoint = other.checkpoint().unwrap();
    assert!(promoted.bind_oauth(&other).is_err());
    assert!(
        promoted
            .receive_oauth(
                &other,
                fresh_effect(&other_checkpoint),
                deliver(&permitted, "channel-two", &fresh)
            )
            .unwrap()
            .is_none()
    );
    assert!(promoted.evidence(&fresh_id).unwrap().is_none());

    assert!(switched.effect_status(&uncertain_id).is_err());
    assert!(
        !promoted
            .reconcile_oauth(&worker, unknown_reconciliation())
            .unwrap()
    );
    assert!(
        retry_uncertain(&promoted, &worker, &revoked)
            .unwrap()
            .is_none()
    );
    assert!(promoted.evidence(&uncertain_id).unwrap().is_none());
    assert_eq!(
        worker.effect_status(&uncertain_id).unwrap(),
        EffectStatus::Unresolved
    );
    assert_eq!(
        worker.effect_status(&fresh_id).unwrap(),
        EffectStatus::Unreserved
    );
    assert_eq!(
        worker.effect_status(&operation).unwrap(),
        EffectStatus::Unresolved
    );
    let recovered = promoted.evidence(&operation).unwrap().unwrap();
    assert_eq!(recovered.outcome, acknowledged.outcome);
    assert_eq!(recovered.journal.actions, acknowledged.journal.actions);
    let recovered_outcomes = [recovered.outcome];
    let later_effect = EffectIdentity {
        operation: "later-independent-effect".into(),
        ..fresh.clone()
    };
    witness
        .append(PrecommitInput {
            current_world: "world",
            effect: &later_effect,
            review: &reviewed_again,
            facts: std::slice::from_ref(&fact),
            publications: &[],
        })
        .unwrap();
    let extended_history = witness.snapshot();
    let extended_audit = AuditAuthority {
        gateway_key: audit.gateway_key,
        log_key,
        facts: audit.facts.clone(),
        minimum_size: 4,
        independent_frontier: Some(
            WitnessFrontier::from_checkpoint(&extended_history.checkpoint, &log_key).unwrap(),
        ),
        review_trust: None,
        prepared_publications: None,
    };
    let late_evidence = |journal, outcomes| DurableEffectRecovery {
        effect: &effect,
        journal,
        outcomes,
        history: &extended_history,
        trust: ProviderAuditTrust {
            authority: &extended_audit,
            provider_key: &provider_key,
        },
    };
    assert!(
        promoted
            .reconcile_oauth(
                &worker,
                DurableEffectRecovery {
                    history: &history,
                    ..late_evidence(&recovered.journal, &recovered_outcomes)
                }
            )
            .is_err()
    );

    let mut changed: crate::gateway::ProviderOutcome =
        crate::gateway::verify(&recovered_outcomes[0], &provider_key).unwrap();
    changed.outcome.action.result = "conflicting-provider-result".into();
    let conflicting_outcomes = [sign(&changed, &provider_signer).unwrap()];
    let conflicting_journal = ProviderJournal::observation(changed.outcome.action);
    let both = [
        recovered_outcomes[0].clone(),
        conflicting_outcomes[0].clone(),
    ];
    for rejected in [
        late_evidence(&absent, &recovered_outcomes),
        late_evidence(&recovered.journal, &[]),
        late_evidence(&recovered.journal, &conflicting_outcomes),
        late_evidence(&recovered.journal, &both),
        late_evidence(&conflicting_journal, &conflicting_outcomes),
    ] {
        assert!(!promoted.reconcile_oauth(&worker, rejected).unwrap());
        assert_eq!(
            worker.effect_status(&operation).unwrap(),
            EffectStatus::Unresolved
        );
    }
    assert!(
        promoted
            .reconcile_oauth(
                &switched,
                late_evidence(&recovered.journal, &recovered_outcomes)
            )
            .is_err()
    );
    assert!(
        promoted
            .reconcile_oauth(
                &worker,
                late_evidence(&recovered.journal, &recovered_outcomes)
            )
            .unwrap()
    );
    let settlement_writer = worker.rotate_writer().unwrap();
    let restarted =
        DurableRefreshLedger::new(&oauth_directory, "receiver-oauth").for_writer(settlement_writer);
    let current_revoked = restarted.checkpoint().unwrap();
    assert!(
        promoted
            .reconcile_oauth(
                &worker,
                late_evidence(&recovered.journal, &recovered_outcomes)
            )
            .is_err()
    );
    // The conflicting pair would pass an audit in isolation, but cannot
    // replace the exact signed outcome already selected by reconciliation.
    assert_eq!(
        crate::gateway::reconcile_intent(
            &conflicting_journal,
            &conflicting_outcomes,
            &extended_history,
            crate::gateway::IntentAuditTrust {
                authority: &extended_audit,
                intent: &intent,
                provider_key: Some(&provider_key),
            },
        ),
        crate::gateway::Reconciliation::default()
    );
    assert!(
        !promoted
            .reconcile_oauth(
                &restarted,
                late_evidence(&conflicting_journal, &conflicting_outcomes)
            )
            .unwrap()
    );
    assert!(
        promoted
            .reconcile_oauth(
                &restarted,
                late_evidence(&recovered.journal, &recovered_outcomes)
            )
            .unwrap()
    );
    let redirected =
        ReceiverDispatch::sign(promoted_cut.clone(), "channel-three", &reapproved, &sender)
            .unwrap();
    assert!(
        promoted
            .receive_oauth(
                &restarted,
                alternate_use(&current_revoked),
                deliver(&redirected, "channel-three", &effect)
            )
            .unwrap()
            .is_none()
    );

    let legacy_dir = durable_directory("receiver-legacy-settlement");
    let mut legacy: serde_json::Value =
        serde_json::from_slice(&std::fs::read(oauth_directory.join("checkpoint.json")).unwrap())
            .unwrap();
    let retained = legacy["effects"][&operation.0].as_object_mut().unwrap();
    assert!(retained.remove("settled_outcome").is_some());
    assert!(retained.remove("recovery_origin").is_some());
    std::fs::write(
        legacy_dir.join("checkpoint.json"),
        serde_json::to_vec(&legacy).unwrap(),
    )
    .unwrap();
    let legacy_reader =
        DurableRefreshLedger::new(&legacy_dir, "receiver-oauth").for_writer(settlement_writer);
    assert_eq!(
        legacy_reader.effect_status(&operation).unwrap(),
        EffectStatus::Reconciled
    );
    assert!(
        !legacy_reader
            .reconcile_effect(late_evidence(&recovered.journal, &recovered_outcomes))
            .unwrap()
    );
    std::fs::remove_dir_all(legacy_dir).unwrap();
    assert_eq!(
        restarted.effect_status(&operation).unwrap(),
        EffectStatus::Reconciled
    );
    assert_eq!(
        restarted.effect_status(&uncertain_id).unwrap(),
        EffectStatus::Unresolved
    );
    assert_eq!(
        promoted.recover_promotion(&committed).unwrap(),
        Some(promoted_cut)
    );
    std::fs::remove_dir_all(other_directory).unwrap();
    std::fs::remove_dir_all(oauth_directory).unwrap();
    std::fs::remove_dir_all(failover).unwrap();
    std::fs::remove_dir_all(receiver_directory).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
}
