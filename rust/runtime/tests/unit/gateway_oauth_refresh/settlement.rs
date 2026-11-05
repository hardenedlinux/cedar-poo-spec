use super::{
    Confirmation, DurableFinalUse, DurableRefreshLedger, actual, digest, durable_directory,
    enroll_with, verified,
};
use crate::gateway::checkpoint_store::CheckpointStage;
use crate::gateway::oauth_refresh_durable::{
    DurableEffectRecovery, DurableEffectUse, EffectStatus,
};
use crate::gateway::provider_durable::{
    DurableReceiver, LegacyReceiverTrust, ManagedDeliveryStage, ReceiverDelivery, ReceiverDispatch,
    ReceiverTrust,
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

#[path = "late_batch.rs"]
mod late_batch;

#[test]
fn concurrent_settlement_survives_lost_acknowledgment_and_handoffs() {
    settlement_race("settlement-race", false, None, &[], false);
}

#[test]
fn legacy_unresolved_requires_trusted_receiver_and_stays_spent() {
    settlement_race("legacy-settlement-race", true, None, &[], false);
}

fn assert_locked(directory: &Path) {
    let file = std::fs::File::open(directory.join("checkpoint.lock")).unwrap();
    assert!(matches!(
        file.try_lock(),
        Err(std::fs::TryLockError::WouldBlock)
    ));
}

fn settlement_race(
    case: &str,
    legacy_migration: bool,
    first: Option<late_batch::FirstCommit>,
    rounds: &[late_batch::RecoveryRound],
    settled_backfill: bool,
) {
    let handoff_first = first.is_some();
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
    let retry = actual(grant.clone(), 14, "settlement-retry");

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
    let batch_effects = [
        "batch-commit",
        "batch-tail",
        "batch-without-evidence",
        "batch-without-receipt",
    ]
    .map(|operation| EffectIdentity {
        operation: operation.into(),
        ..effect.clone()
    });
    let batch_operations = batch_effects
        .each_ref()
        .map(|entry| OperationId(entry.operation.clone()));
    let batch_intents: Vec<_> = if handoff_first {
        batch_effects
            .iter()
            .map(|entry| {
                witness
                    .append(PrecommitInput {
                        current_world: "world",
                        effect: entry,
                        review: &review,
                        facts: std::slice::from_ref(&fact),
                        publications: &[],
                    })
                    .unwrap()
            })
            .collect()
    } else {
        Vec::new()
    };
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
    let mut late_outcome = None;
    for (index, (entry, intent)) in batch_effects.iter().zip(&batch_intents).enumerate() {
        let current = actual(grant.clone(), 14, &entry.operation);
        let input = DurableEffectUse {
            admission: DurableFinalUse {
                checked: &initial,
                replica: &initial,
                current: &current,
                base_allowed: true,
            },
            effect: entry,
            intent,
            history: &history,
            trust,
        };
        let dispatch =
            ReceiverDispatch::sign(active.cut().unwrap(), "original", intent, &sender).unwrap();
        let delivery = ReceiverDelivery {
            authorization: &dispatch,
            channel: "original",
            effect: entry,
            bindings: std::slice::from_ref(&fact),
            facts: &facts,
            publications: &[],
        };
        if index == 2 {
            assert!(
                active
                    .crash_receive_oauth(
                        &oauth,
                        input,
                        delivery,
                        ManagedDeliveryStage::OAuthReserved,
                    )
                    .is_err()
            );
        } else {
            let outcome = active
                .receive_oauth(&oauth, input, delivery)
                .unwrap()
                .unwrap();
            if index == 3 {
                late_outcome = Some(outcome);
            }
        }
    }
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
    if handoff_first {
        for operation in &batch_operations {
            assert!(
                legacy["effects"][&operation.0]
                    .as_object_mut()
                    .unwrap()
                    .remove("recovery_origin")
                    .is_some()
            );
        }
    }
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
        let (migration_result, promoted, handed_writer) = std::thread::scope(|scope| {
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
                open().rotate_writer()
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
        let writer = handed_writer.unwrap();
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
    let (writer, successor_cut, final_replica) = if handoff_first {
        let current_receiver = receiver(&successor);
        assert_eq!(
            writer.legacy_unresolved_operations().unwrap(),
            batch_operations
        );
        let committed = current_receiver
            .evidence(&batch_operations[0])
            .unwrap()
            .unwrap();
        let tail = current_receiver
            .evidence(&batch_operations[1])
            .unwrap()
            .unwrap();
        assert!(
            current_receiver
                .evidence(&batch_operations[2])
                .unwrap()
                .is_none()
        );
        let committed_outcome = [committed.outcome];
        let tail_outcome = [tail.outcome];
        let empty = ProviderJournal::default();
        let item = |index, journal, outcomes| DurableEffectRecovery {
            effect: &batch_effects[index],
            journal,
            outcomes,
            ..evidence(&settled.journal, &signed)
        };
        let batch = || {
            [
                evidence(&settled.journal, &signed),
                item(2, &empty, &[]),
                item(0, &committed.journal, &committed_outcome),
                item(1, &tail.journal, &tail_outcome),
                item(3, &empty, &[]),
            ]
        };
        let fenced =
            current_receiver.migrate_legacy_oauth_batch(&standby_writer, batch(), &trusted);
        assert!(fenced.confirmed.is_empty());
        assert_eq!(fenced.stopped.unwrap().operation, operation);
        let expected = current_receiver.acknowledged_checkpoint().unwrap();
        std::fs::copy(
            successor.join("checkpoint.json"),
            primary.join("checkpoint.json"),
        )
        .unwrap();
        let replacement = receiver(&primary);
        let (partial, overlap, next_writer, next_cut) = std::thread::scope(|scope| {
            let (durable, durable_seen) = mpsc::channel();
            let (release, commit_release) = mpsc::channel();
            let (started, overlap_started) = mpsc::channel();
            let (between, overlap_between) = mpsc::channel();
            let (continue_overlap, overlap_release) = mpsc::channel();
            let old_receiver = &current_receiver;
            let old_writer = &writer;
            let lost_item = &batch_operations[0];
            let migration_trust = &trusted;
            let first = scope.spawn(move || {
                old_receiver.migrate_legacy_oauth_batch_at(
                    old_writer,
                    batch(),
                    migration_trust,
                    |item, stage| {
                        assert_eq!(item, lost_item);
                        if stage == CheckpointStage::Durable {
                            durable.send(()).unwrap();
                            commit_release.recv().map_err(|error| error.to_string())?;
                            Err("batch acknowledgment lost".into())
                        } else {
                            Ok(())
                        }
                    },
                )
            });
            durable_seen.recv().unwrap();
            assert_locked(&oauth_path);
            assert_locked(&pin);
            let second =
                scope.spawn(move || {
                    let [_, missing, repeated, suffix, _] = batch();
                    started.send(()).unwrap();
                    let items = [repeated, missing, suffix].into_iter().enumerate().map(
                        |(index, input)| {
                            if index == 1 {
                                between.send(()).unwrap();
                                overlap_release.recv().unwrap();
                            }
                            input
                        },
                    );
                    old_receiver.migrate_legacy_oauth_batch_at(
                        old_writer,
                        items,
                        migration_trust,
                        |_, _| panic!("the overlapping worker attempted another write"),
                    )
                });
            overlap_started.recv().unwrap();
            release.send(()).unwrap();
            overlap_between.recv().unwrap();
            let cut = replacement.promote(&expected).unwrap();
            let current = open().for_writer(writer.rotate_writer().unwrap());
            continue_overlap.send(()).unwrap();
            (first.join().unwrap(), second.join().unwrap(), current, cut)
        });
        assert_eq!(
            overlap.confirmed,
            std::slice::from_ref(&batch_operations[0])
        );
        assert!(overlap.pending.is_empty());
        let overlap_stop = overlap.stopped.unwrap();
        assert_eq!(overlap_stop.operation, batch_operations[2]);
        assert_eq!(overlap_stop.error, "OAuth writer fenced");
        let stale_replica = current_receiver.migrate_legacy_oauth_batch(
            &next_writer,
            batch().into_iter().skip(1),
            &trusted,
        );
        assert!(stale_replica.confirmed.is_empty() && stale_replica.pending.is_empty());
        let replica_stop = stale_replica.stopped.unwrap();
        assert_eq!(replica_stop.operation, batch_operations[2]);
        assert_eq!(
            replica_stop.error,
            "receiver replica differs from the independent checkpoint"
        );
        let writer = next_writer;
        let current_receiver = replacement;
        let successor_cut = next_cut;
        assert_eq!(partial.confirmed, std::slice::from_ref(&operation));
        assert_eq!(partial.pending, std::slice::from_ref(&batch_operations[2]));
        let stopped = partial.stopped.unwrap();
        assert_eq!(stopped.operation, batch_operations[0]);
        assert_eq!(stopped.error, "batch acknowledgment lost");
        assert_eq!(
            writer.legacy_unresolved_operations().unwrap(),
            &batch_operations[1..]
        );
        let resumed = current_receiver.migrate_legacy_oauth_batch_at(
            &writer,
            batch(),
            &trusted,
            |item, _| {
                assert_eq!(item, &batch_operations[1]);
                Ok(())
            },
        );
        assert_eq!(
            resumed.confirmed,
            [
                operation.clone(),
                batch_operations[0].clone(),
                batch_operations[1].clone()
            ]
        );
        assert_eq!(resumed.pending, &batch_operations[2..]);
        assert!(resumed.stopped.is_none());
        assert_eq!(
            writer.legacy_unresolved_operations().unwrap(),
            &batch_operations[2..]
        );
        std::thread::scope(|scope| {
            let repeat = || {
                current_receiver.migrate_legacy_oauth_batch_at(
                    &writer,
                    batch(),
                    &trusted,
                    |_, _| panic!("repeating a completed batch wrote another checkpoint"),
                )
            };
            let concurrent = scope.spawn(repeat);
            assert_eq!(repeat(), resumed);
            assert_eq!(concurrent.join().unwrap(), resumed);
        });
        let checkpoint = writer.checkpoint().unwrap();
        let dispatch = ReceiverDispatch::sign(
            successor_cut.clone(),
            "batch-retry",
            &batch_intents[0],
            &sender,
        )
        .unwrap();
        assert!(
            current_receiver
                .receive_oauth(
                    &writer,
                    DurableEffectUse {
                        effect: &batch_effects[0],
                        intent: &batch_intents[0],
                        admission: DurableFinalUse {
                            checked: &checkpoint,
                            replica: &checkpoint,
                            current: &retry,
                            base_allowed: true,
                        },
                        history: &history,
                        trust,
                    },
                    ReceiverDelivery {
                        authorization: &dispatch,
                        channel: "batch-retry",
                        effect: &batch_effects[0],
                        bindings: std::slice::from_ref(&fact),
                        facts: &facts,
                        publications: &[],
                    },
                )
                .unwrap()
                .is_none()
        );
        let writer_cut = writer.rotate_writer().unwrap();
        let (writer_cut, successor_cut, final_replica) = late_batch::replay_across_processes(
            &directory,
            late_batch::RestartFixture {
                active: primary.clone(),
                retired: successor.clone(),
                writer: writer_cut,
                retired_writer: None,
                previous: expected,
                fact: fact.clone(),
                history: history.clone(),
                effect: batch_effects[3].clone(),
                prefix: batch_effects[0].clone(),
                missing: batch_effects[2].clone(),
                missing_intent: batch_intents[2].clone(),
                grant: grant.clone(),
                round: 0,
                first_worker: late_batch::Worker::A,
            },
            late_outcome.as_ref().unwrap(),
            first.unwrap(),
            rounds,
            settled_backfill,
        );
        let writer = open().for_writer(writer_cut);
        assert_eq!(
            writer.legacy_unresolved_operations().unwrap(),
            std::slice::from_ref(&batch_operations[2])
        );
        (writer, successor_cut, final_replica)
    } else {
        (writer, successor_cut, successor.clone())
    };
    let latest = writer.checkpoint().unwrap();
    let new_dispatch =
        ReceiverDispatch::sign(successor_cut, "after-revocation", &intent, &sender).unwrap();
    assert!(
        receiver(&final_replica)
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
