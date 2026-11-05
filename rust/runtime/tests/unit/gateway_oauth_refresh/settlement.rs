use super::{
    Confirmation, DurableFinalUse, DurableRefreshLedger, actual, digest, durable_directory,
    enroll_with, verified,
};
use crate::gateway::checkpoint_store::CheckpointStage;
use crate::gateway::oauth_refresh_durable::{
    DurableEffectRecovery, DurableEffectUse, EffectStatus,
};
use crate::gateway::provider_durable::{
    DurableReceiver, ReceiverDelivery, ReceiverDispatch, ReceiverTrust,
};
use crate::gateway::wire::{sign, simulation_key};
use crate::gateway::witness::PrecommitInput;
use crate::gateway::{
    AuditAuthority, EffectIdentity, FactAuthority, FactBinding, IntentAuditTrust, Origin,
    ProviderAuditTrust, ProviderJournal, ProviderOutcome, Reconciliation, ReviewBinding, Witness,
    WitnessFrontier, reconcile_intent, verify,
};
use cedar_poo_core::operation_identity::OperationId;
use std::path::Path;
use std::sync::mpsc;

#[test]
fn concurrent_settlement_survives_lost_acknowledgment_and_handoffs() {
    let directory = durable_directory("settlement-race");
    let oauth_path = directory.join("oauth");
    let pin = directory.join("pin");
    let primary = directory.join("primary");
    let standby = directory.join("standby");
    let successor = directory.join("successor");
    for path in [&oauth_path, &pin, &primary, &standby, &successor] {
        std::fs::create_dir(path).unwrap();
    }
    let open = || DurableRefreshLedger::new(&oauth_path, "settlement-race");
    let oauth = open();
    oauth.initialize().unwrap();
    let grant = enroll_with(Confirmation::Dpop("key".into()), |input| {
        oauth.enroll(input).unwrap()
    });
    let current = actual(grant.clone(), 14, "settlement-first");
    let retry = actual(grant, 14, "settlement-retry");

    let effect = EffectIdentity {
        operation: "settled-operation".into(),
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
    let issuer = simulation_key(3);
    let facts = [sign(&fact, &issuer).unwrap()];
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
    let history = witness.snapshot();
    let log_key = witness.verifying_key();
    let sender = simulation_key(4);
    let provider = simulation_key(8);
    let audit = AuditAuthority {
        gateway_key: *sender.verifying_key(),
        log_key,
        facts: FactAuthority::new(
            vec![fact.clone()],
            [(fact.issuer.clone(), *issuer.verifying_key())].into(),
            14,
        )
        .unwrap(),
        minimum_size: 1,
        independent_frontier: Some(
            WitnessFrontier::from_checkpoint(&history.checkpoint, &log_key).unwrap(),
        ),
        review_trust: None,
        prepared_publications: None,
    };
    let trust = ProviderAuditTrust {
        authority: &audit,
        provider_key: provider.verifying_key(),
    };
    let receiver = |path| {
        DurableReceiver::managed(
            path,
            &pin,
            ReceiverTrust {
                scope: "settlement-race",
                sender: sender.verifying_key(),
                witness: &log_key,
                provider: &provider,
            },
        )
        .unwrap()
    };
    let active = receiver(&primary);
    active.initialize().unwrap();
    active.bind_oauth(&oauth).unwrap();
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
    let dispatch =
        ReceiverDispatch::sign(active.cut().unwrap(), "original", &intent, &sender).unwrap();
    let delivery = ReceiverDelivery {
        authorization: &dispatch,
        channel: "original",
        effect: &effect,
        bindings: std::slice::from_ref(&fact),
        facts: &facts,
        publications: &[],
    };
    let initial = oauth.checkpoint().unwrap();
    let signed = active
        .receive_oauth(&oauth, use_effect(&initial, &current), delivery)
        .unwrap()
        .unwrap();
    let operation = OperationId(effect.operation.clone());
    let original = active.evidence(&operation).unwrap().unwrap();
    assert_eq!(original.outcome, signed);
    let signed = [signed];
    let mut conflict: ProviderOutcome = verify(&signed[0], provider.verifying_key()).unwrap();
    conflict.outcome.action.result = "different completion".into();
    let signed_conflict = [sign(&conflict, &provider).unwrap()];
    let conflicting = ProviderJournal::observation(conflict.outcome.action);
    let evidence = |journal, outcomes| DurableEffectRecovery {
        effect: &effect,
        journal,
        outcomes,
        history: &history,
        trust,
    };
    for (journal, outcomes) in [
        (&original.journal, &signed),
        (&conflicting, &signed_conflict),
    ] {
        assert_eq!(
            reconcile_intent(
                journal,
                outcomes,
                &history,
                IntentAuditTrust {
                    authority: &audit,
                    intent: &intent,
                    provider_key: Some(provider.verifying_key()),
                }
            ),
            Reconciliation::default()
        );
    }
    assert!(
        oauth
            .reconcile_effect_at(evidence(&original.journal, &signed), |stage| {
                assert!(stage == CheckpointStage::Staged);
                Err("settlement stopped before commit".into())
            })
            .is_err()
    );
    assert_eq!(
        open().effect_status(&operation).unwrap(),
        EffectStatus::Unresolved
    );

    std::thread::scope(|scope| {
        let (staged, staged_observed) = mpsc::channel();
        let (release, proceed) = mpsc::channel();
        let (started, contender_started) = mpsc::channel();
        let original_input = evidence(&original.journal, &signed);
        let conflict_input = evidence(&conflicting, &signed_conflict);
        let first = scope.spawn(move || {
            open().reconcile_effect_at(original_input, |stage| match stage {
                CheckpointStage::Staged => {
                    staged.send(()).unwrap();
                    proceed.recv().map_err(|error| error.to_string())
                }
                CheckpointStage::Durable => Err("settlement acknowledgment lost".into()),
            })
        });
        staged_observed.recv().unwrap();
        let second = scope.spawn(move || {
            started.send(()).unwrap();
            open().reconcile_effect(conflict_input)
        });
        contender_started.recv().unwrap();
        release.send(()).unwrap();
        assert_eq!(
            first.join().unwrap().unwrap_err(),
            "settlement acknowledgment lost"
        );
        assert!(!second.join().unwrap().unwrap());
    });
    assert_eq!(
        open().effect_status(&operation).unwrap(),
        EffectStatus::Reconciled
    );

    let promote = |from, to| {
        std::fs::copy(
            Path::join(from, "checkpoint.json"),
            Path::join(to, "checkpoint.json"),
        )
        .unwrap();
        let expected = receiver(from).acknowledged_checkpoint().unwrap();
        receiver(to).promote(&expected).unwrap()
    };
    let standby_cut = promote(&primary, &standby);
    let standby_writer = open().for_writer(oauth.rotate_writer().unwrap());
    let changed_route = ReceiverDispatch::sign(standby_cut, "retry", &intent, &sender).unwrap();
    let standby_checkpoint = standby_writer.checkpoint().unwrap();
    assert!(
        receiver(&standby)
            .receive_oauth(
                &standby_writer,
                use_effect(&standby_checkpoint, &retry),
                ReceiverDelivery {
                    authorization: &changed_route,
                    channel: "retry",
                    effect: &effect,
                    bindings: std::slice::from_ref(&fact),
                    facts: &facts,
                    publications: &[],
                }
            )
            .unwrap()
            .is_none()
    );
    assert!(standby_writer.revoke(verified(digest())).unwrap());

    let successor_cut = promote(&standby, &successor);
    let writer = open().for_writer(standby_writer.rotate_writer().unwrap());
    let settled = receiver(&successor).evidence(&operation).unwrap().unwrap();
    assert_eq!(settled.outcome, signed[0]);
    assert!(
        standby_writer
            .reconcile_effect(evidence(&original.journal, &signed))
            .is_err()
    );
    assert!(
        writer
            .reconcile_effect_at(evidence(&settled.journal, &signed), |_| {
                panic!("idempotent confirmation attempted to rewrite the settlement")
            })
            .unwrap()
    );
    assert!(
        !writer
            .reconcile_effect(evidence(&conflicting, &signed_conflict))
            .unwrap()
    );
    assert_eq!(
        writer.effect_status(&operation).unwrap(),
        EffectStatus::Reconciled
    );
    let latest = writer.checkpoint().unwrap();
    let new_dispatch =
        ReceiverDispatch::sign(successor_cut, "after-revocation", &intent, &sender).unwrap();
    assert!(
        receiver(&successor)
            .receive_oauth(
                &writer,
                use_effect(&latest, &retry),
                ReceiverDelivery {
                    authorization: &new_dispatch,
                    channel: "after-revocation",
                    effect: &effect,
                    bindings: std::slice::from_ref(&fact),
                    facts: &facts,
                    publications: &[],
                }
            )
            .unwrap()
            .is_none()
    );
    assert!(
        !writer
            .execute_final(use_effect(&latest, &retry).admission, || {
                panic!("settlement revived a revoked grant")
            })
            .unwrap()
    );
    std::fs::remove_dir_all(directory).unwrap();
}
