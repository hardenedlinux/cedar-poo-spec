use super::{
    Confirmation, DurableFinalUse, DurableRefreshLedger, actual, digest, durable_directory,
    enroll_with, verified,
};
use crate::gateway::checkpoint_store::CheckpointStage;
use crate::gateway::oauth_refresh_durable::{
    DurableEffectRecovery, DurableEffectUse, EffectStatus,
};
use crate::gateway::provider_durable::{
    DurableReceiver, LegacyReceiverTrust, ReceiverDelivery, ReceiverDispatch, ReceiverTrust,
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
    settlement_race("settlement-race", false, false);
}

#[test]
fn legacy_unresolved_requires_trusted_receiver_and_stays_spent() {
    settlement_race("legacy-settlement-race", true, false);
}

#[test]
fn legacy_migration_rejects_writer_and_replica_fenced_by_handoffs() {
    settlement_race("legacy-handoff-first", true, true);
}

fn assert_locked(directory: &Path) {
    let file = std::fs::File::open(directory.join("checkpoint.lock")).unwrap();
    assert!(matches!(
        file.try_lock(),
        Err(std::fs::TryLockError::WouldBlock)
    ));
}

fn settlement_race(case: &str, legacy_migration: bool, handoff_first: bool) {
    let directory = durable_directory(case);
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
        !active
            .reconcile_oauth(&oauth, evidence(&conflicting, &signed_conflict))
            .unwrap()
    );
    assert!(
        !oauth
            .reconcile_effect(evidence(&original.journal, &signed))
            .unwrap()
    );
    assert_eq!(
        oauth.effect_status(&operation).unwrap(),
        EffectStatus::Unresolved
    );

    let legacy_path = directory.join("legacy-oauth");
    std::fs::create_dir(&legacy_path).unwrap();
    let mut legacy: serde_json::Value =
        serde_json::from_slice(&std::fs::read(oauth_path.join("checkpoint.json")).unwrap())
            .unwrap();
    assert!(
        legacy["effects"][&operation.0]
            .as_object_mut()
            .unwrap()
            .remove("recovery_origin")
            .is_some()
    );
    std::fs::write(
        legacy_path.join("checkpoint.json"),
        serde_json::to_vec(&legacy).unwrap(),
    )
    .unwrap();
    let legacy_oauth = DurableRefreshLedger::new(&legacy_path, "settlement-race");
    assert!(
        !legacy_oauth
            .reconcile_effect(evidence(&original.journal, &signed))
            .unwrap()
    );
    assert_eq!(
        legacy_oauth.effect_status(&operation).unwrap(),
        EffectStatus::Unresolved
    );

    if legacy_migration {
        // Reproduce the old on-disk schema in the same OAuth authority
        // directory recorded in the receiver checkpoint.
        std::fs::write(
            oauth_path.join("checkpoint.json"),
            serde_json::to_vec(&legacy).unwrap(),
        )
        .unwrap();
        active.advance(&active.cut().unwrap()).unwrap();
    }

    let copied_pin = directory.join("foreign-pin");
    std::fs::create_dir(&copied_pin).unwrap();
    std::fs::copy(
        pin.join("checkpoint.json"),
        copied_pin.join("checkpoint.json"),
    )
    .unwrap();
    let foreign = DurableReceiver::managed(
        &primary,
        &copied_pin,
        ReceiverTrust {
            scope: "settlement-race",
            sender: sender.verifying_key(),
            witness: &log_key,
            provider: &provider,
        },
    )
    .unwrap();
    assert_eq!(
        foreign.evidence(&operation).unwrap().unwrap().outcome,
        signed[0]
    );
    assert!(
        !foreign
            .reconcile_oauth(&oauth, evidence(&original.journal, &signed))
            .unwrap()
    );
    let trusted = LegacyReceiverTrust::from_config(&pin, "settlement-race").unwrap();
    let migration = legacy_migration.then_some(&trusted);
    if legacy_migration {
        assert!(
            !active
                .reconcile_oauth(&oauth, evidence(&original.journal, &signed))
                .unwrap()
        );
        assert!(
            !active
                .migrate_legacy_oauth(&oauth, evidence(&original.journal, &[]), &trusted)
                .unwrap()
        );
        assert!(
            !active
                .migrate_legacy_oauth(&oauth, evidence(&conflicting, &signed_conflict), &trusted)
                .unwrap()
        );
        assert!(
            !foreign
                .migrate_legacy_oauth(&oauth, evidence(&original.journal, &signed), &trusted)
                .unwrap()
        );
        let wrong_scope = LegacyReceiverTrust::from_config(&pin, "foreign-scope").unwrap();
        assert!(
            !active
                .migrate_legacy_oauth(&oauth, evidence(&original.journal, &signed), &wrong_scope)
                .unwrap()
        );
        assert!(
            !active
                .migrate_legacy_oauth(
                    &legacy_oauth,
                    evidence(&original.journal, &signed),
                    &trusted
                )
                .unwrap()
        );
        assert_eq!(
            oauth.effect_status(&operation).unwrap(),
            EffectStatus::Unresolved
        );
    }
    assert!(
        active
            .reconcile_oauth_at(
                &oauth,
                evidence(&original.journal, &signed),
                migration,
                |stage| {
                    assert!(stage == CheckpointStage::Staged);
                    Err("settlement stopped before commit".into())
                }
            )
            .is_err()
    );
    assert_eq!(
        open().effect_status(&operation).unwrap(),
        EffectStatus::Unresolved
    );

    if legacy_migration {
        let staged: serde_json::Value =
            serde_json::from_slice(&std::fs::read(oauth_path.join("checkpoint.json")).unwrap())
                .unwrap();
        assert!(
            staged["effects"][&operation.0]
                .get("recovery_origin")
                .is_none()
        );
        assert!(
            staged["effects"][&operation.0]
                .get("settled_outcome")
                .is_none()
        );
    }

    let (current_replica, next_replica, current_writer) = if handoff_first {
        std::fs::copy(
            primary.join("checkpoint.json"),
            standby.join("checkpoint.json"),
        )
        .unwrap();
        let expected = active.acknowledged_checkpoint().unwrap();
        let standby_receiver = receiver(&standby);
        let (migration_result, promoted, revoked_writer) = std::thread::scope(|scope| {
            let (staged, staged_observed) = mpsc::channel();
            let (release, proceed) = mpsc::channel();
            let (handoff_started, handoff_ready) = mpsc::channel();
            let (revoke_started, revoke_ready) = mpsc::channel();
            let original_input = evidence(&original.journal, &signed);
            let old_receiver = &active;
            let migrating = scope.spawn(move || {
                old_receiver.reconcile_oauth_at(&open(), original_input, migration, |stage| {
                    assert!(stage == CheckpointStage::Staged);
                    staged.send(()).unwrap();
                    proceed.recv().map_err(|error| error.to_string())?;
                    Err("migration interrupted before checkpoint install".into())
                })
            });
            staged_observed.recv().unwrap();
            assert_locked(&pin);
            assert_locked(&oauth_path);
            let promoting = scope.spawn(move || {
                handoff_started.send(()).unwrap();
                standby_receiver.promote(&expected)
            });
            let revoking = scope.spawn(move || {
                revoke_started.send(()).unwrap();
                let writer = open().rotate_writer()?;
                let current = open().for_writer(writer);
                assert!(current.revoke(verified(digest()))?);
                Ok::<_, String>(writer)
            });
            handoff_ready.recv().unwrap();
            revoke_ready.recv().unwrap();
            release.send(()).unwrap();
            (
                migrating.join().unwrap(),
                promoting.join().unwrap(),
                revoking.join().unwrap(),
            )
        });
        assert_eq!(
            migration_result.unwrap_err(),
            "migration interrupted before checkpoint install"
        );
        promoted.unwrap();
        let writer = revoked_writer.unwrap();
        let current = open().for_writer(writer);
        assert_eq!(
            current.effect_status(&operation).unwrap(),
            EffectStatus::Unresolved
        );
        assert!(
            receiver(&standby)
                .migrate_legacy_oauth(&oauth, evidence(&original.journal, &signed), &trusted)
                .is_err()
        );
        assert!(
            active
                .migrate_legacy_oauth(&current, evidence(&original.journal, &signed), &trusted)
                .is_err()
        );
        assert_eq!(
            current.effect_status(&operation).unwrap(),
            EffectStatus::Unresolved
        );
        (&standby, &primary, Some(writer))
    } else {
        (&primary, &standby, None)
    };
    let current_oauth = || {
        let ledger = open();
        match current_writer {
            Some(writer) => ledger.for_writer(writer),
            None => ledger,
        }
    };
    let active = receiver(current_replica);
    let oauth = current_oauth();

    let promote_during_commit = legacy_migration && !handoff_first;
    let competing_handoff = promote_during_commit.then(|| {
        std::fs::copy(
            current_replica.join("checkpoint.json"),
            next_replica.join("checkpoint.json"),
        )
        .unwrap();
        (
            receiver(next_replica),
            active.acknowledged_checkpoint().unwrap(),
        )
    });
    let committed_cut = std::thread::scope(|scope| {
        let (staged, staged_observed) = mpsc::channel();
        let (release, proceed) = mpsc::channel();
        let (started, contender_started) = mpsc::channel();
        let original_input = evidence(&original.journal, &signed);
        let conflict_input = evidence(&conflicting, &signed_conflict);
        let receiver = &active;
        let first = scope.spawn(move || {
            receiver.reconcile_oauth_at(&current_oauth(), original_input, migration, |stage| {
                match stage {
                    CheckpointStage::Staged => {
                        staged.send(()).unwrap();
                        proceed.recv().map_err(|error| error.to_string())
                    }
                    CheckpointStage::Durable => Err("settlement acknowledgment lost".into()),
                }
            })
        });
        staged_observed.recv().unwrap();
        assert_locked(&pin);
        assert_locked(&oauth_path);
        let second = scope.spawn(move || {
            started.send(()).unwrap();
            if let Some(trusted) = migration {
                receiver.migrate_legacy_oauth(&current_oauth(), conflict_input, trusted)
            } else {
                receiver.reconcile_oauth(&current_oauth(), conflict_input)
            }
        });
        contender_started.recv().unwrap();
        let competing = competing_handoff.map(|(standby, expected)| {
            let (promotion_started, promotion_ready) = mpsc::channel();
            let (revocation_started, revocation_ready) = mpsc::channel();
            let promoting = scope.spawn(move || {
                promotion_started.send(()).unwrap();
                standby.promote(&expected)
            });
            let revoking = scope.spawn(move || {
                revocation_started.send(()).unwrap();
                current_oauth().revoke(verified(digest()))
            });
            promotion_ready.recv().unwrap();
            revocation_ready.recv().unwrap();
            (promoting, revoking)
        });
        release.send(()).unwrap();
        assert_eq!(
            first.join().unwrap().unwrap_err(),
            "settlement acknowledgment lost"
        );
        match second.join().unwrap() {
            Ok(accepted) => assert!(!accepted),
            Err(error) => {
                assert!(promote_during_commit);
                assert_eq!(
                    error,
                    "receiver replica differs from the independent checkpoint"
                );
            }
        }
        competing.map(|(promoting, revoking)| {
            assert!(revoking.join().unwrap().unwrap());
            promoting.join().unwrap().unwrap()
        })
    });
    assert_eq!(
        current_oauth().effect_status(&operation).unwrap(),
        EffectStatus::Reconciled
    );

    if legacy_migration {
        let committed: serde_json::Value =
            serde_json::from_slice(&std::fs::read(oauth_path.join("checkpoint.json")).unwrap())
                .unwrap();
        let retained = &committed["effects"][&operation.0];
        assert!(retained.get("recovery_origin").is_some());
        assert_eq!(
            retained["settled_outcome"],
            signed[0].source_sha256().unwrap()
        );
        assert!(
            receiver(if promote_during_commit {
                next_replica
            } else {
                current_replica
            })
            .reconcile_oauth_at(
                &oauth,
                evidence(&original.journal, &signed),
                migration,
                |_| { panic!("legacy confirmation attempted a second checkpoint write") }
            )
            .unwrap()
        );
    }

    let promote = |from, to| {
        std::fs::copy(
            Path::join(from, "checkpoint.json"),
            Path::join(to, "checkpoint.json"),
        )
        .unwrap();
        let expected = receiver(from).acknowledged_checkpoint().unwrap();
        receiver(to).promote(&expected).unwrap()
    };
    let standby_cut = committed_cut.unwrap_or_else(|| promote(current_replica, next_replica));
    let standby_writer = open().for_writer(oauth.rotate_writer().unwrap());
    let changed_route = ReceiverDispatch::sign(standby_cut, "retry", &intent, &sender).unwrap();
    let standby_checkpoint = standby_writer.checkpoint().unwrap();
    assert!(
        receiver(next_replica)
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
    if !handoff_first && !promote_during_commit {
        assert!(standby_writer.revoke(verified(digest())).unwrap());
    }

    let successor_cut = promote(next_replica, &successor);
    let writer = open().for_writer(standby_writer.rotate_writer().unwrap());
    let settled = receiver(&successor).evidence(&operation).unwrap().unwrap();
    assert_eq!(settled.outcome, signed[0]);
    assert!(
        receiver(next_replica)
            .reconcile_oauth(&writer, evidence(&settled.journal, &signed))
            .is_err()
    );
    assert!(
        receiver(&successor)
            .reconcile_oauth(&standby_writer, evidence(&original.journal, &signed))
            .is_err()
    );
    assert!(
        receiver(&successor)
            .reconcile_oauth_at(&writer, evidence(&settled.journal, &signed), None, |_| {
                panic!("idempotent confirmation attempted to rewrite the settlement")
            })
            .unwrap()
    );
    assert!(
        !receiver(&successor)
            .reconcile_oauth(&writer, evidence(&conflicting, &signed_conflict))
            .unwrap()
    );
    assert_eq!(
        writer.effect_status(&operation).unwrap(),
        EffectStatus::Reconciled
    );
    if legacy_migration {
        assert!(
            receiver(&successor)
                .migrate_legacy_oauth(&writer, evidence(&settled.journal, &signed), &trusted)
                .unwrap()
        );
        assert!(
            !receiver(&successor)
                .migrate_legacy_oauth(&writer, evidence(&conflicting, &signed_conflict), &trusted)
                .unwrap()
        );
    }
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
