use super::{setup, signed};
use crate::gateway::{
    EffectIo, ProviderJournal, Reconciliation, RecoveryEvidence, Simulator, Witness,
};
use p256::ecdsa::SigningKey;

#[test]
fn gateway_lost_receipt_resolves_only_from_independent_provider_evidence() {
    for revoked in [false, true] {
        let (_, _, first) = setup();
        let mut witness = Witness::simulation();
        let mut provider = ProviderJournal::default();
        let envelope = first.envelope();
        let (outcome, receipt) = first
            .execute(
                first.prepare(&envelope).unwrap(),
                &envelope,
                EffectIo {
                    witness: &mut witness,
                    provider: &mut provider,
                    crash_after_send: true,
                },
            )
            .unwrap();
        assert!(outcome.unknown && receipt.is_none());
        let proofs: Vec<_> = provider.signed_outcomes().cloned().collect();
        assert_eq!(proofs.len(), 1);
        let audit = first.audit_authority(&witness);
        assert_eq!(
            crate::gateway::reconcile_provider_outcomes(
                &provider,
                &proofs,
                &witness.snapshot(),
                crate::gateway::ProviderAuditTrust {
                    authority: &audit,
                    provider_key: &first.provider_verifying_key()
                }
            ),
            Reconciliation::default()
        );
        first.advance_time(100).unwrap();
        if revoked {
            first.revoke().unwrap();
        }
        let old_window = first.lifecycle_view().unwrap();
        let raw = Simulator::recover(
            &first,
            RecoveryEvidence {
                witness: &witness,
                publications: &[],
                audit: &audit,
                receipts: &[],
                provider: &provider,
            },
        )
        .unwrap();
        assert!(raw.lifecycle_view().unwrap().unknown);
        let settled = Simulator::recover_with_provider_outcomes(
            &raw,
            RecoveryEvidence {
                witness: &witness,
                publications: &[],
                audit: &audit,
                receipts: &[],
                provider: &provider,
            },
            &proofs,
        )
        .unwrap();
        let view = settled.lifecycle_view().unwrap();
        assert!(view.spent && !view.unknown && view.mediator_current);
        assert_eq!(view.revoked, revoked);
        assert_eq!(view.now, old_window.now);
        assert_eq!(view.fact_generation, old_window.fact_generation);
        assert_eq!(view.world, old_window.world);
        assert!(settled.prepare(&settled.envelope()).is_err());
        assert!(raw.advance_time(101).is_err());
        let repeated = Simulator::recover_with_provider_outcomes(
            &settled,
            RecoveryEvidence {
                witness: &witness,
                publications: &[],
                audit: &audit,
                receipts: &[],
                provider: &provider,
            },
            &proofs,
        )
        .unwrap();
        assert!(
            repeated.lifecycle_view().unwrap().spent && !repeated.lifecycle_view().unwrap().unknown
        );
        assert_eq!(provider.actions.len(), 1);
        let imported: ProviderJournal =
            serde_json::from_value(serde_json::to_value(&provider).unwrap()).unwrap();
        assert_eq!(imported.signed_outcomes().count(), 0);
    }
}

#[test]
fn gateway_provider_outcome_refuses_wrong_signer_domain_version_and_missing_observation() {
    let (_, _, first) = setup();
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
                crash_after_send: true,
            },
        )
        .unwrap();
    let proof = provider.signed_outcomes().next().unwrap().clone();
    let audit = first.audit_authority(&witness);
    let provider_key = SigningKey::from_slice(&[8; 32]).unwrap();
    let original: crate::gateway::ProviderOutcome =
        crate::gateway::verify(&proof, provider_key.verifying_key()).unwrap();
    let mut forged = proof.clone();
    forged.signature[0] ^= 1;
    let mut wrong_domain = original.clone();
    wrong_domain.domain = "gateway-receipt".into();
    let mut wrong_version = original.clone();
    wrong_version.version.major = 2;
    let mut wrong_log = original.clone();
    wrong_log.log_key = first
        .verifying_key()
        .to_encoded_point(false)
        .as_bytes()
        .to_vec();
    let mut wrong_action = original.clone();
    wrong_action.outcome.action.effect.generation += 1;
    let mut missing_facts = original.clone();
    missing_facts.outcome.facts.clear();
    let wrong_signer = SigningKey::from_slice(&[3; 32]).unwrap();
    let controls = vec![
        forged,
        signed(&wrong_domain, &provider_key),
        signed(&wrong_version, &provider_key),
        signed(&wrong_log, &provider_key),
        signed(&wrong_action, &provider_key),
        signed(&missing_facts, &provider_key),
        signed(&original, &wrong_signer),
    ];
    for invalid in controls {
        let branch = first.fork_simulation().unwrap();
        let report = crate::gateway::reconcile_provider_outcomes(
            &provider,
            std::slice::from_ref(&invalid),
            &witness.snapshot(),
            crate::gateway::ProviderAuditTrust {
                authority: &audit,
                provider_key: &branch.provider_verifying_key(),
            },
        );
        assert_eq!(report.invalid_receipts, 1);
        let recovered = Simulator::recover_with_provider_outcomes(
            &branch,
            RecoveryEvidence {
                witness: &witness,
                publications: &[],
                audit: &audit,
                receipts: &[],
                provider: &provider,
            },
            &[invalid],
        )
        .unwrap();
        assert!(recovered.lifecycle_view().unwrap().unknown);
        assert!(recovered.lifecycle_view().unwrap().spent);
        assert!(recovered.prepare(&recovered.envelope()).is_err());
    }
    let empty = ProviderJournal::default();
    let report = crate::gateway::reconcile_provider_outcomes(
        &empty,
        std::slice::from_ref(&proof),
        &witness.snapshot(),
        crate::gateway::ProviderAuditTrust {
            authority: &audit,
            provider_key: &first.provider_verifying_key(),
        },
    );
    assert_eq!(
        report.missing_actions,
        vec![envelope.effect.operation.clone()]
    );
    let duplicate = crate::gateway::reconcile_provider_outcomes(
        &provider,
        &[proof.clone(), proof],
        &witness.snapshot(),
        crate::gateway::ProviderAuditTrust {
            authority: &audit,
            provider_key: &first.provider_verifying_key(),
        },
    );
    assert_eq!(duplicate.duplicates, vec![envelope.effect.operation]);
    assert!(
        Simulator::recover_with_provider_outcomes(
            &first,
            RecoveryEvidence {
                witness: &witness,
                publications: &[],
                audit: &audit,
                receipts: &[signed(&original, &provider_key)],
                provider: &provider,
            },
            &[]
        )
        .is_err()
    );
    assert!(first.lifecycle_view().unwrap().mediator_current);
}

#[test]
fn unsigned_observations_cannot_create_provider_authority_or_erase_send_records() {
    let (case, schema, first) = setup();
    let mut witness = Witness::simulation();
    let mut imported: ProviderJournal = serde_json::from_str("{\"actions\":[]}").unwrap();
    let envelope = first.envelope();
    let (_, receipt) = first
        .execute(
            first.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut imported,
                crash_after_send: false,
            },
        )
        .unwrap();
    assert!(receipt.is_none() && imported.actions.is_empty());
    assert!(first.lifecycle_view().unwrap().unknown);
    assert_eq!(imported.signed_outcomes().count(), 0);
    let live = Simulator::new(&case, Some(&schema)).unwrap();
    let mut provider = ProviderJournal::default();
    let envelope = live.envelope();
    live.execute(
        live.prepare(&envelope).unwrap(),
        &envelope,
        EffectIo {
            witness: &mut witness,
            provider: &mut provider,
            crash_after_send: true,
        },
    )
    .unwrap();
    provider.actions.clear();
    let duplicate = Simulator::new(&case, Some(&schema)).unwrap();
    let envelope = duplicate.envelope();
    let (_, receipt) = duplicate
        .execute(
            duplicate.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    assert!(receipt.is_none() && provider.actions.is_empty());
    assert_eq!(provider.signed_outcomes().count(), 1);
    assert!(duplicate.lifecycle_view().unwrap().unknown);
}

#[test]
fn provider_settlement_retains_a_replaced_resource_image() {
    let (_, _, first) = setup();
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
                crash_after_send: true,
            },
        )
        .unwrap();
    let outcomes: Vec<_> = provider.signed_outcomes().cloned().collect();
    let audit = first.audit_authority(&witness);
    first
        .replace_resource("replacement-incarnation".into(), 8)
        .unwrap();
    let replacement = first.envelope().effect;
    let recovered = Simulator::recover_with_provider_outcomes(
        &first,
        RecoveryEvidence {
            witness: &witness,
            publications: &[],
            audit: &audit,
            receipts: &[],
            provider: &provider,
        },
        &outcomes,
    )
    .unwrap();
    assert!(
        !recovered.lifecycle_view().unwrap().unknown,
        "authenticated original completion stayed unresolved after replacement"
    );
    assert_eq!(recovered.envelope().effect, replacement);
    assert!(recovered.lifecycle_view().unwrap().spent);
    assert!(recovered.prepare(&recovered.envelope()).is_err());
    assert_eq!(provider.actions.len(), 1);
}
