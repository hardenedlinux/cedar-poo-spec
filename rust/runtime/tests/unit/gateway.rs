use super::{receipt, validated};
use crate::gateway::{
    AuditAuthority, EffectIo, Envelope, FactAuthority, FactBinding, Fault, Lineage, LogSnapshot,
    Origin, ProviderJournal, Reconciliation, RecoveryEvidence, Signed, Simulator, Version, Witness,
    reconcile, verify_log,
};
use p256::ecdsa::{Signature, SigningKey, signature::Signer};
use std::sync::{Arc, Barrier};

fn setup() -> (crate::Case, cedar_poo_core::SchemaSourceJson, Simulator) {
    let case = receipt();
    let schema = validated(case.clone()).schema;
    let simulator = Simulator::new(&case, Some(&schema)).unwrap();
    (case, schema, simulator)
}
fn signed(value: &impl serde::Serialize, key: &SigningKey) -> Signed {
    let payload = serde_json::to_vec(value).unwrap();
    let signature: Signature = key.sign(&payload);
    Signed {
        payload,
        signature: signature.to_bytes().to_vec(),
    }
}
#[test]
fn gateway_real_signature_preparation_keeps_source_inventory_time_and_key_checks() {
    let key = SigningKey::from_slice(&[11; 32]).unwrap();
    let other = SigningKey::from_slice(&[12; 32]).unwrap();
    let fact = FactBinding {
        issuer: "idp".into(),
        subject: "user".into(),
        audience: "gateway".into(),
        source: "idp/mfa".into(),
        field: "mfa".into(),
        value: "true|not-a-delimiter".into(),
        generation: 9,
        origin: Origin::Attested,
        not_before: 1,
        expires_at: 20,
    };
    let evidence = vec![signed(&fact, &key)];
    let authority = || {
        FactAuthority::new(
            vec![fact.clone()],
            [("idp".into(), *key.verifying_key())].into(),
            10,
        )
        .unwrap()
    };
    assert!(authority().accepts(&evidence).is_ok());
    let prepared = authority().prepare_sources(&evidence).unwrap();
    assert_eq!(
        prepared.accepts(&evidence).unwrap(),
        authority().accepts(&evidence).unwrap()
    );
    assert!(prepared.accepts(&[signed(&fact, &other)]).is_err());
    assert!(prepared.accepts(&[]).is_err());
    assert!(
        prepared
            .accepts(&[evidence[0].clone(), evidence[0].clone()])
            .is_err()
    );
    for changed in [
        FactBinding {
            generation: 10,
            ..fact.clone()
        },
        FactBinding {
            subject: "other".into(),
            ..fact.clone()
        },
        FactBinding {
            origin: Origin::Claimed,
            ..fact.clone()
        },
        FactBinding {
            audience: "other".into(),
            ..fact.clone()
        },
    ] {
        assert!(prepared.accepts(&[signed(&changed, &key)]).is_err());
    }
    assert!(prepared.at_time(20).unwrap().accepts(&evidence).is_err());
    assert!(prepared.at_time(9).is_err());
    let expired = FactAuthority::new(
        vec![fact.clone()],
        [("idp".into(), *key.verifying_key())].into(),
        20,
    )
    .unwrap();
    assert!(expired.accepts(&evidence).is_err());
    let replaced = FactAuthority::new(
        vec![fact],
        [("idp".into(), *other.verifying_key())].into(),
        10,
    )
    .unwrap();
    assert!(replaced.accepts(&evidence).is_err());
}
#[test]
fn gateway_handle_is_foreign_stale_single_use_and_unknown_survives_recovery() {
    let (_, _, first) = setup();
    let (_, _, other) = setup();
    let envelope = first.envelope();
    let mut log = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let foreign = other.prepare(&other.envelope()).unwrap();
    assert!(
        first
            .execute(
                foreign,
                &envelope,
                EffectIo {
                    witness: &mut log,
                    provider: &mut provider,
                    crash_after_send: false
                },
            )
            .is_err()
    );
    let stale = first.prepare(&envelope).unwrap();
    first.mutate(Fault::None, &mut first.envelope()).unwrap();
    assert!(
        first
            .execute(
                stale,
                &envelope,
                EffectIo {
                    witness: &mut log,
                    provider: &mut provider,
                    crash_after_send: false
                },
            )
            .is_err()
    );
    let token = first.prepare(&envelope).unwrap();
    let (outcome, receipt) = first
        .execute(
            token,
            &envelope,
            EffectIo {
                witness: &mut log,
                provider: &mut provider,
                crash_after_send: true,
            },
        )
        .unwrap();
    assert!(outcome.unknown && receipt.is_none());
    assert!(first.prepare(&envelope).is_err());
    let recovered = Simulator::recover(
        &first,
        RecoveryEvidence {
            publications: &[],
            audit: &first.audit_authority(&log),
            witness: &log,
            receipts: &[],
            provider: &provider,
        },
    )
    .unwrap();
    assert!(recovered.prepare(&recovered.envelope()).is_err());
    assert_eq!(provider.actions.len(), 1);
    assert_eq!(
        reconcile(
            &provider,
            &[],
            &log.snapshot(),
            &first.audit_authority(&log)
        )
        .missing_receipts,
        vec![envelope.effect.operation]
    );
}
#[test]
fn gateway_resource_replacement_and_revocation_before_use_refuse() {
    for fault in [Fault::Revoked, Fault::Expired] {
        let (_, _, simulator) = setup();
        let mut envelope = simulator.envelope();
        let token = simulator.prepare(&envelope).unwrap();
        simulator.mutate(fault, &mut envelope).unwrap();
        let mut log = Witness::simulation();
        let mut provider = ProviderJournal::default();
        assert!(
            simulator
                .execute(
                    token,
                    &envelope,
                    EffectIo {
                        witness: &mut log,
                        provider: &mut provider,
                        crash_after_send: false
                    },
                )
                .is_err()
        );
        assert!(log.entries().is_empty() && provider.actions.is_empty());
    }
    let (_, _, simulator) = setup();
    let envelope = simulator.envelope();
    let token = simulator.prepare(&envelope).unwrap();
    simulator.replace_resource("new-inode".into(), 8).unwrap();
    assert!(
        simulator
            .execute(
                token,
                &envelope,
                EffectIo {
                    witness: &mut Witness::simulation(),
                    provider: &mut ProviderJournal::default(),
                    crash_after_send: false
                },
            )
            .is_err()
    );
}
#[test]
fn gateway_concurrent_preparations_commit_one_effect() {
    let (_, _, simulator) = setup();
    let simulator = Arc::new(simulator);
    let barrier = Arc::new(Barrier::new(2));
    let workers: Vec<_> = (0..2)
        .map(|_| {
            let simulator = Arc::clone(&simulator);
            let barrier = Arc::clone(&barrier);
            std::thread::spawn(move || {
                let envelope = simulator.envelope();
                let handle = simulator.prepare(&envelope).unwrap();
                barrier.wait();
                simulator
                    .execute(
                        handle,
                        &envelope,
                        EffectIo {
                            witness: &mut Witness::simulation(),
                            provider: &mut ProviderJournal::default(),
                            crash_after_send: false,
                        },
                    )
                    .is_ok()
            })
        })
        .collect();
    assert_eq!(
        workers
            .into_iter()
            .map(|worker| worker.join().unwrap())
            .filter(|passed| *passed)
            .count(),
        1
    );
}
#[test]
fn gateway_independent_audit_and_lineage_do_not_confuse_commit_with_effect() {
    let (_, _, simulator) = setup();
    let envelope = simulator.envelope();
    let mut log = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let (_, receipt) = simulator
        .execute(
            simulator.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut log,
                provider: &mut provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    let receipts = vec![receipt.unwrap()];
    assert_eq!(
        reconcile(
            &provider,
            &receipts,
            &log.snapshot(),
            &simulator.audit_authority(&log)
        ),
        Reconciliation::default()
    );
    let lineage = Lineage::from_witness(&log, &provider).unwrap();
    let graph = serde_json::to_value(lineage.export()).unwrap();
    let source = graph["edges"][0]["source"].as_str().unwrap().to_string();
    assert!(
        lineage
            .affected(&[source])
            .contains(&envelope.effect.operation)
    );
    assert!(lineage.affected(&["absent".into()]).is_empty());
    assert!(
        graph["edges"]
            .as_array()
            .unwrap()
            .iter()
            .all(|edge| edge["state"] == "provider-observed")
    );
    let missing = ProviderJournal::default();
    let intents =
        serde_json::to_value(Lineage::from_witness(&log, &missing).unwrap().export()).unwrap();
    assert!(
        intents["edges"]
            .as_array()
            .unwrap()
            .iter()
            .all(|edge| edge["state"] == "precommitted-only")
    );
    let recovered = Simulator::recover(
        &simulator,
        RecoveryEvidence {
            publications: &[],
            audit: &simulator.audit_authority(&log),
            witness: &log,
            receipts: &receipts,
            provider: &provider,
        },
    )
    .unwrap();
    assert!(recovered.prepare(&recovered.envelope()).is_err());
    provider.actions[0].effect.payload = "other".into();
    assert_eq!(
        reconcile(
            &provider,
            &receipts,
            &log.snapshot(),
            &simulator.audit_authority(&log)
        )
        .mismatched
        .len(),
        1
    );
    let mut damaged_snapshot = log.snapshot();
    damaged_snapshot.entries.clear();
    assert!(
        reconcile(
            &provider,
            &receipts,
            &damaged_snapshot,
            &simulator.audit_authority(&log)
        )
        .invalid_log
    );
}
#[test]
fn gateway_wire_rejects_unknown_duplicate_and_incompatible_fields() {
    let (_, _, simulator) = setup();
    let mut envelope = simulator.envelope();
    envelope.version.minor = 1;
    assert!(simulator.prepare(&envelope).is_err());
    let mut wire = serde_json::to_value(simulator.envelope()).unwrap();
    wire["effect"]["untrusted"] = true.into();
    assert!(serde_json::from_value::<Envelope>(wire).is_err());
    assert!(serde_json::from_str::<Version>(r#"{"major":1,"major":2,"minor":0}"#).is_err());
}

#[test]
fn gateway_public_auditor_needs_no_signer_and_refuses_old_checkpoint() {
    let (_, _, simulator) = setup();
    let envelope = simulator.envelope();
    let mut log = Witness::simulation();
    let old = log.snapshot();
    let mut provider = ProviderJournal::default();
    let (_, receipt) = simulator
        .execute(
            simulator.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut log,
                provider: &mut provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    let encoded = serde_json::to_vec(&log.snapshot()).unwrap();
    let snapshot: LogSnapshot = serde_json::from_slice(&encoded).unwrap();
    let authority = AuditAuthority {
        prepared_publications: None,
        gateway_key: simulator.verifying_key(),
        log_key: log.verifying_key(),
        facts: simulator.fact_authority(),
        minimum_size: 1,
        review_trust: None,
    };
    let receipts = vec![receipt.unwrap()];
    assert_eq!(
        reconcile(&provider, &receipts, &snapshot, &authority),
        Reconciliation::default()
    );
    assert!(reconcile(&provider, &receipts, &old, &authority).invalid_log);
    let unrelated = SigningKey::from_slice(&[20; 32]).unwrap();
    assert!(verify_log(&snapshot, unrelated.verifying_key(), 1).is_err());
}

#[test]
fn gateway_corrupted_witness_refuses_dispatch_and_pending_precommit_is_not_clean() {
    let (_, _, simulator) = setup();
    let envelope = simulator.envelope();
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    simulator
        .execute(
            simulator.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    let report = reconcile(
        &ProviderJournal::default(),
        &[],
        &witness.snapshot(),
        &simulator.audit_authority(&witness),
    );
    assert_eq!(
        report.unresolved_precommits,
        vec![envelope.effect.operation.clone()]
    );
    assert_ne!(report, Reconciliation::default());
    // Independent provider enumeration and the witness are distinct inputs.
    // Losing both outcome and provider visibility must leave an explicit intent.
    for truncate in [true, false] {
        let fresh = setup().2;
        let mut damaged = Witness::simulation();
        let mut scratch = ProviderJournal::default();
        fresh
            .execute(
                fresh.prepare(&envelope).unwrap(),
                &envelope,
                EffectIo {
                    witness: &mut damaged,
                    provider: &mut scratch,
                    crash_after_send: false,
                },
            )
            .unwrap();
        let floor = damaged.entries().len() as u64;
        let mut untrusted = damaged.snapshot();
        if truncate {
            untrusted.entries.clear();
        } else {
            untrusted.entries[0].signature[0] ^= 1;
        }
        assert!(Witness::restore(&untrusted, floor).is_err());
        assert!(scratch.actions.len() == 1);
    }
}

#[test]
fn gateway_operation_identity_encodes_typed_fields_without_delimiter_aliasing() {
    let (mut left, schema, _) = setup();
    let mut right = left.clone();
    left.revision = "a/b".into();
    left.name = "c".into();
    right.revision = "a".into();
    right.name = "b/c".into();
    assert_eq!(
        format!("{}/{}", left.revision, left.name),
        format!("{}/{}", right.revision, right.name)
    );
    // Current revision validation already excludes this slash ambiguity.
    assert!(Simulator::new(&left, Some(&schema)).is_err());
    assert_ne!(
        crate::json_sha256(&("cedar-poo-operation-v1", &left.revision, &left.name)).unwrap(),
        crate::json_sha256(&("cedar-poo-operation-v1", &right.revision, &right.name)).unwrap()
    );
    left.revision = "a-b".into();
    left.name = "c".into();
    right.revision = "a".into();
    right.name = "b-c".into();
    let first = Simulator::new(&left, Some(&schema)).unwrap();
    let second = Simulator::new(&right, Some(&schema)).unwrap();
    assert_eq!(
        first.envelope().effect.operation,
        crate::json_sha256(&("cedar-poo-operation-v1", &left.revision, &left.name)).unwrap()
    );
    assert_ne!(
        first.envelope().effect.operation,
        second.envelope().effect.operation
    );
    assert!(second.prepare(&first.envelope()).is_err());
}

#[test]
fn gateway_post_send_receipt_budget_failure_retains_unknown_without_a_false_complete() {
    let (mut case, schema, _) = setup();
    case.request.resource = format!("Document::\"{}\"", "x".repeat(500_000));
    let simulator = Simulator::new(&case, Some(&schema)).unwrap();
    let envelope = simulator.envelope();
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let (outcome, receipt) = simulator
        .execute(
            simulator.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    assert!(outcome.admitted && outcome.precommitted && outcome.sent && outcome.unknown);
    assert!(!outcome.receipted && receipt.is_none());
    assert_eq!(provider.actions.len(), 1);
    assert!(simulator.prepare(&envelope).is_err());
    let report = reconcile(
        &provider,
        &[],
        &witness.snapshot(),
        &simulator.audit_authority(&witness),
    );
    assert_eq!(
        report.unresolved_precommits,
        vec![envelope.effect.operation.clone()]
    );
    assert_eq!(report.missing_receipts, vec![envelope.effect.operation]);
    assert!(!report.invalid_log);
}

#[test]
fn gateway_owned_witness_restores_verified_bytes_and_extends_the_same_prefix() {
    let (case, schema, first) = setup();
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let envelope = first.envelope();
    first
        .execute(
            first.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    let snapshot = witness.snapshot();
    let mut restored = Witness::restore(&snapshot, 1).unwrap();
    let mut next = case;
    next.name.push_str("-next-operation");
    let next = Simulator::new(&next, Some(&schema)).unwrap();
    let envelope = next.envelope();
    let (outcome, _) = next
        .execute(
            next.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut restored,
                provider: &mut provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    assert!(outcome.receipted);
    assert_eq!(snapshot.entries.len(), 1);
    assert_eq!(restored.entries().len(), 2);
    restored.verify_history().unwrap();
    assert!(Witness::restore(&snapshot, 2).is_err());
    let mut changed = snapshot;
    changed.entries[0].payload[0] ^= 1;
    assert!(Witness::restore(&changed, 1).is_err());
}

#[test]
fn gateway_source_statements_preserve_independent_field_authority_and_exact_coverage() {
    use crate::gateway::FactStatement;
    let left_key = SigningKey::from_slice(&[11; 32]).unwrap();
    let right_key = SigningKey::from_slice(&[12; 32]).unwrap();
    let left = FactBinding {
        issuer: "left".into(),
        subject: "user".into(),
        audience: "gateway".into(),
        source: "world".into(),
        field: "a".into(),
        value: "1".into(),
        generation: 3,
        origin: Origin::Attested,
        not_before: 1,
        expires_at: 20,
    };
    let second = FactBinding {
        field: "b".into(),
        value: "2".into(),
        ..left.clone()
    };
    let right = FactBinding {
        issuer: "right".into(),
        field: "c".into(),
        ..left.clone()
    };
    let authority = FactAuthority::new(
        vec![left.clone(), second.clone(), right.clone()],
        [
            ("left".into(), *left_key.verifying_key()),
            ("right".into(), *right_key.verifying_key()),
        ]
        .into(),
        10,
    )
    .unwrap();
    let statement = FactStatement {
        version: Version { major: 1, minor: 0 },
        facts: vec![left.clone(), second.clone()],
    };
    let right_statement = FactStatement {
        facts: vec![right.clone()],
        ..statement.clone()
    };
    let evidence = vec![
        signed(&statement, &left_key),
        signed(&right_statement, &right_key),
    ];
    let individual = vec![
        signed(&left, &left_key),
        signed(&second, &left_key),
        signed(&right, &right_key),
    ];
    let expected = authority.accepts(&individual).unwrap();
    assert_eq!(authority.accepts(&evidence).unwrap(), expected);
    let prepared = authority.clone().prepare_sources(&evidence).unwrap();
    assert_eq!(prepared.accepts(&evidence).unwrap(), expected);
    let reversed = vec![evidence[1].clone(), evidence[0].clone()];
    assert_eq!(prepared.accepts(&reversed).unwrap().len(), 3);
    assert!(prepared.at_time(20).unwrap().accepts(&evidence).is_err());
    assert!(prepared.accepts(&evidence[..1]).is_err());
    assert!(
        prepared
            .accepts(&[evidence[0].clone(), evidence[0].clone()])
            .is_err()
    );
    assert!(
        prepared
            .accepts(&[signed(&statement, &right_key), evidence[1].clone()])
            .is_err()
    );
    for changed in [
        FactStatement {
            facts: vec![],
            ..statement.clone()
        },
        FactStatement {
            version: Version { major: 1, minor: 1 },
            ..statement.clone()
        },
        FactStatement {
            facts: vec![left.clone(), left.clone()],
            ..statement.clone()
        },
        FactStatement {
            facts: vec![left.clone(), second.clone(), right.clone()],
            ..statement.clone()
        },
        FactStatement {
            facts: vec![
                left.clone(),
                FactBinding {
                    generation: 4,
                    ..second.clone()
                },
            ],
            ..statement.clone()
        },
        FactStatement {
            facts: vec![
                left.clone(),
                FactBinding {
                    origin: Origin::Claimed,
                    ..second.clone()
                },
            ],
            ..statement.clone()
        },
    ] {
        assert!(
            prepared
                .accepts(&[signed(&changed, &left_key), evidence[1].clone()])
                .is_err()
        );
    }
    let mut unknown = serde_json::to_value(&statement).unwrap();
    unknown["verified"] = serde_json::Value::Bool(true);
    assert!(
        prepared
            .accepts(&[signed(&unknown, &left_key), evidence[1].clone()])
            .is_err()
    );
    let mut altered = evidence.clone();
    altered[0].signature[0] ^= 1;
    assert!(prepared.accepts(&altered).is_err());
    let changed_keys = FactAuthority::new(
        expected.clone(),
        [
            ("left".into(), *right_key.verifying_key()),
            ("right".into(), *right_key.verifying_key()),
        ]
        .into(),
        10,
    )
    .unwrap();
    assert!(changed_keys.accepts(&evidence).is_err());
}

#[test]
fn gateway_an_outcome_resolves_only_its_exact_precommit_and_duplicate_intents_quarantine_recovery()
{
    for changed_effect in [false, true] {
        check_ambiguous_intent_recovery(changed_effect);
    }
}

fn check_ambiguous_intent_recovery(changed_effect: bool) {
    let (case, schema, first) = setup();
    let mut witness = Witness::simulation();
    let mut earlier_provider = ProviderJournal::default();
    let first_envelope = first.envelope();
    first
        .execute(
            first.prepare(&first_envelope).unwrap(),
            &first_envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut earlier_provider,
                crash_after_send: true,
            },
        )
        .unwrap();
    assert!(first.lifecycle_view().unwrap().unknown);
    let mut later_case = case;
    if changed_effect {
        later_case.request.resource = "Document::\"two\"".into();
    }
    let second = Simulator::new(&later_case, Some(&schema)).unwrap();
    let envelope = second.envelope();
    assert_eq!(first_envelope.effect.operation, envelope.effect.operation);
    assert_eq!(first_envelope.effect == envelope.effect, !changed_effect);
    let mut observed = ProviderJournal::default();
    let (_, receipt) = second
        .execute(
            second.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut observed,
                crash_after_send: false,
            },
        )
        .unwrap();
    let receipts = vec![receipt.unwrap()];
    let audit = second.audit_authority(&witness);
    let report = reconcile(&observed, &receipts, &witness.snapshot(), &audit);
    assert!(!report.invalid_log);
    assert_eq!(report.invalid_receipts, 0);
    assert_eq!(
        report.unresolved_precommits,
        vec![envelope.effect.operation.clone()]
    );
    assert_eq!(report.duplicates, vec![envelope.effect.operation]);
    let recovered = Simulator::recover(
        &first,
        RecoveryEvidence {
            witness: &witness,
            publications: &[],
            audit: &audit,
            receipts: &receipts,
            provider: &observed,
        },
    )
    .unwrap();
    assert!(recovered.lifecycle_view().unwrap().unknown);
    assert!(recovered.prepare(&recovered.envelope()).is_err());
}

#[test]
fn gateway_clean_alternate_history_cannot_resolve_the_retained_intent() {
    for renewed in [false, true] {
        for revoked in [false, true] {
            check_retained_history_after_controls(renewed, revoked);
        }
    }
}

fn check_retained_history_after_controls(renewed: bool, revoked: bool) {
    let (case, schema, first) = setup();
    first.refresh_facts(&case, 200).unwrap();
    let mut original_log = Witness::simulation();
    let mut original_provider = ProviderJournal::default();
    let envelope = first.envelope();
    first
        .execute(
            first.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut original_log,
                provider: &mut original_provider,
                crash_after_send: true,
            },
        )
        .unwrap();
    if renewed {
        first.refresh_facts(&case, 300).unwrap();
    }
    if revoked {
        first.revoke().unwrap();
    }
    assert!(first.lifecycle_view().unwrap().unknown);
    let second = Simulator::new(&case, Some(&schema)).unwrap();
    let mut alternate_log = Witness::simulation();
    let mut alternate_provider = ProviderJournal::default();
    let other = second.envelope();
    assert_eq!(envelope.effect, other.effect);
    let (_, receipt) = second
        .execute(
            second.prepare(&other).unwrap(),
            &other,
            EffectIo {
                witness: &mut alternate_log,
                provider: &mut alternate_provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    assert_ne!(
        original_log.entries()[0].payload,
        alternate_log.entries()[0].payload
    );
    let receipts = vec![receipt.unwrap()];
    let audit = second.audit_authority(&alternate_log);
    assert_eq!(
        reconcile(
            &alternate_provider,
            &receipts,
            &alternate_log.snapshot(),
            &audit
        ),
        Reconciliation::default()
    );
    let before = first.lifecycle_view().unwrap();
    let recovered = Simulator::recover(
        &first,
        RecoveryEvidence {
            witness: &alternate_log,
            publications: &[],
            audit: &audit,
            receipts: &receipts,
            provider: &alternate_provider,
        },
    );
    assert!(
        recovered.is_err(),
        "a clean but different log resolved the retained intent"
    );
    assert_eq!(first.lifecycle_view().unwrap(), before);
    assert!(first.prepare(&first.envelope()).is_err());
}
