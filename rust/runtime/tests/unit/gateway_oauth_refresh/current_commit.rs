use super::{
    Confirmation, DurableFinalUse, DurableRefreshLedger, actual, digest, durable_directory,
    enroll_for_audience, verified,
};
use crate::gateway::checkpoint_store::CheckpointStage;
use crate::gateway::oauth::CurrentUse;
use crate::gateway::oauth_refresh_durable::{
    CurrentEffectUse, DelegatedPaymentUse, DurableEffectRecovery, DurableEffectUse,
    DurableRevocationCheckpoint, EffectCheckpoint, EffectStatus,
};
use crate::gateway::provider_durable::{
    DurableReceiver, ManagedDeliveryStage, ReceiverDelivery, ReceiverDispatch, ReceiverTrust,
};
use crate::gateway::wire::simulation_key;
use crate::gateway::{
    AuditAuthority, Envelope, LogSnapshot, PreparedEffect, ProviderAuditTrust, Signed, Simulator,
    Witness, WitnessFrontier,
};
use cedar_poo_commerce::admission::{
    CommerceAdmissionHost, DelegatedAdmissionRequest, SignedDelegation,
};
use cedar_poo_commerce::projection::{
    LeanMandateClaims, LeanOfferClaims, mandate_claims, offer_claims,
};
use cedar_poo_commerce::signatures::{
    MandateOfferTrust, MandatePayload, OfferPayload, PrincipalId, delegation_signing_bytes,
    sha256_hex,
};
use cedar_poo_core::{SchemaSourceJson, operation_identity::OperationId};
use p256::ecdsa::{Signature, SigningKey, VerifyingKey, signature::Signer};
use serde_json::json;

struct Intent<'a> {
    simulator: &'a Simulator,
    envelope: Envelope,
    signed: Signed,
    history: LogSnapshot,
    audit: AuditAuthority,
}

impl<'a> Intent<'a> {
    fn prepare(simulator: &'a Simulator) -> (Self, PreparedEffect) {
        let envelope = simulator.envelope();
        let prepared = simulator.prepare(&envelope).unwrap();
        let mut witness = Witness::simulation();
        let signed = simulator
            .precommit(&prepared, &envelope, &mut witness)
            .unwrap();
        let history = witness.snapshot();
        let mut audit = simulator.audit_authority(&witness);
        audit.independent_frontier =
            Some(WitnessFrontier::from_checkpoint(&history.checkpoint, &audit.log_key).unwrap());
        (
            Self {
                simulator,
                envelope,
                signed,
                history,
                audit,
            },
            prepared,
        )
    }

    fn input<'b>(
        &'b self,
        prepared: PreparedEffect,
        current: &'b CurrentUse,
        checked: &'b DurableRevocationCheckpoint,
        pin: &'b EffectCheckpoint,
        provider: &'b VerifyingKey,
        payment: Option<DelegatedPaymentUse<'b>>,
    ) -> CurrentEffectUse<'b> {
        CurrentEffectUse {
            simulator: self.simulator,
            prepared,
            envelope: &self.envelope,
            checkpoint: pin,
            authorization: DurableEffectUse {
                admission: DurableFinalUse {
                    checked,
                    replica: checked,
                    current,
                    base_allowed: false,
                },
                effect: &self.envelope.effect,
                intent: &self.signed,
                history: &self.history,
                trust: ProviderAuditTrust {
                    authority: &self.audit,
                    provider_key: provider,
                },
            },
            payment,
        }
    }

    fn id(&self) -> OperationId {
        OperationId(self.envelope.effect.operation.clone())
    }
}

fn oauth_current(grant: &crate::gateway::oauth::Grant, proof: &str) -> CurrentUse {
    let mut current = actual(grant.clone(), 14, proof);
    current.target.audience.clone_from(&grant.audiences[0]);
    current.target.required_scopes.clone_from(&grant.scopes);
    current
}

#[test]
fn current_commit_rejects_changed_facts_and_a_valid_older_image() {
    let path = durable_directory("current-commit-rollback");
    let ledger = DurableRefreshLedger::new(&path, "authority");
    ledger.initialize().unwrap();
    let grant = enroll_for_audience(
        Confirmation::Dpop("key".into()),
        "initial",
        "fhir",
        |input| ledger.enroll(input).unwrap(),
    );
    let checked = ledger.checkpoint().unwrap();
    let pin = ledger.effect_checkpoint().unwrap();
    let checkpoint_file = path.join("checkpoint.json");
    let old_bytes = std::fs::read(&checkpoint_file).unwrap();
    let case = crate::bridge::tests::receipt();
    let schema = crate::bridge::tests::validated(case.clone()).schema;
    let simulator =
        Simulator::new_for_oauth(&case, &schema, oauth_current(&grant, "configured").target)
            .unwrap();
    simulator.advance_time(14).unwrap();
    let (old, prepared) = Intent::prepare(&simulator);
    let mut changed = case;
    changed.entities = serde_json::from_value(json!([
        {"uid":{"type":"Document","id":"one"},"attrs":{},"parents":[]}
    ]))
    .unwrap();
    simulator.refresh_facts(&changed, 100).unwrap();
    assert_ne!(
        simulator.envelope().current_world,
        old.envelope.current_world
    );
    assert!(simulator.lifecycle_view().unwrap().cedar_allowed);
    let provider = simulator.provider_verifying_key();
    let use_effect = oauth_current(&grant, "first");
    assert!(
        ledger
            .execute_current(
                old.input(prepared, &use_effect, &checked, &pin, &provider, None),
                |_| panic!("stale Cedar evidence released an effect"),
            )
            .unwrap_err()
            .contains("stale effect handle")
    );
    assert!(ledger.recover_effects(&pin).unwrap());

    let (current, prepared) = Intent::prepare(&simulator);
    assert_eq!(
        ledger
            .execute_current(
                current.input(prepared, &use_effect, &checked, &pin, &provider, None),
                |_| Err("completion reply lost".into()),
            )
            .unwrap_err(),
        "completion reply lost"
    );
    let full = ledger.effect_checkpoint().unwrap();
    let committed_bytes = std::fs::read(&checkpoint_file).unwrap();
    assert!(ledger.recover(&checked).unwrap());
    assert_eq!(
        ledger.effect_status(&current.id()).unwrap(),
        EffectStatus::Unresolved
    );
    assert!(!ledger.recover_effects(&pin).unwrap());

    std::fs::write(&checkpoint_file, old_bytes).unwrap();
    let reopened = DurableRefreshLedger::new(&path, "authority");
    assert!(reopened.recover(&checked).unwrap());
    assert!(!reopened.recover_effects(&full).unwrap());
    let (retry, prepared) = Intent::prepare(&simulator);
    let use_effect = oauth_current(&grant, "retry");
    assert!(
        !reopened
            .execute_current(
                retry.input(prepared, &use_effect, &checked, &full, &provider, None),
                |_| panic!("older image released the original effect"),
            )
            .unwrap()
    );
    std::fs::write(&checkpoint_file, committed_bytes).unwrap();
    assert!(reopened.recover_effects(&full).unwrap());
    assert_eq!(
        reopened.effect_status(&retry.id()).unwrap(),
        EffectStatus::Unresolved
    );
    std::fs::remove_dir_all(path).unwrap();
}

#[test]
fn current_commit_rejects_a_published_deny_after_prepare() {
    use crate::gateway::{
        AnalysisKind, PublicationDelivery, ReviewAuthority, ReviewRecord, ReviewSubmission,
    };

    let path = durable_directory("current-commit-publication");
    let ledger = DurableRefreshLedger::new(&path, "authority");
    ledger.initialize().unwrap();
    let grant = enroll_for_audience(
        Confirmation::Dpop("key".into()),
        "initial",
        "fhir",
        |input| ledger.enroll(input).unwrap(),
    );
    let current = oauth_current(&grant, "stale-publication");
    let checked = ledger.checkpoint().unwrap();
    let pin = ledger.effect_checkpoint().unwrap();
    let mut candidate = crate::bridge::tests::receipt();
    let schema = crate::bridge::tests::validated(candidate.clone()).schema;
    let simulator = Simulator::new_for_oauth(&candidate, &schema, current.target.clone()).unwrap();
    simulator.advance_time(14).unwrap();
    let (old, prepared) = Intent::prepare(&simulator);
    let mut policies = (*candidate.policies).clone();
    policies["staticPolicies"]["base"]["effect"] = json!("forbid");
    candidate.policies = serde_json::from_value(policies).unwrap();
    candidate.expected = "deny".into();
    let original = &old.envelope.review;
    let signed = ReviewAuthority::simulation()
        .certify(&ReviewRecord {
            version: old.envelope.version.clone(),
            before_root: candidate.revision.clone(),
            after_root: "restricted".into(),
            before: original.after.clone(),
            after: crate::value_sha256(&candidate.policies).unwrap(),
            schema: original.schema.clone(),
            source: original.after.clone(),
            epoch: original.epoch,
            analysis: AnalysisKind::NoGain,
            evidence: "fixture replaces the only permit with a forbid".into(),
        })
        .unwrap();
    let ticket = simulator
        .register_review(ReviewSubmission {
            review: &signed,
            candidate: &candidate,
            approval: None,
        })
        .unwrap();
    let published = simulator
        .publish_review(ticket, PublicationDelivery::Complete)
        .unwrap();
    assert_eq!(published.epoch, original.epoch + 1);
    assert!(!simulator.lifecycle_view().unwrap().cedar_allowed);
    let provider = simulator.provider_verifying_key();
    assert!(
        ledger
            .execute_current(
                old.input(prepared, &current, &checked, &pin, &provider, None),
                |_| panic!("superseded policy released an effect"),
            )
            .unwrap_err()
            .contains("stale effect handle")
    );
    assert!(ledger.recover_effects(&pin).unwrap());
    assert_eq!(
        ledger.effect_status(&old.id()).unwrap(),
        EffectStatus::Unreserved
    );
    std::fs::remove_dir_all(path).unwrap();
}

struct SignedPurchase {
    root: MandatePayload,
    child: MandatePayload,
    offer: OfferPayload,
    lineage: Vec<LeanMandateClaims>,
    claims: LeanOfferClaims,
    root_signature: [u8; 64],
    child_signature: [u8; 64],
    offer_signature: [u8; 64],
    checkout: String,
}

impl SignedPurchase {
    fn new(principal: &SigningKey, agent: &SigningKey, merchant: &SigningKey, branch: u8) -> Self {
        let checkout = format!("checkout-{branch}");
        let root = MandatePayload {
            mandate_id: "payment-root".into(),
            principal: PrincipalId {
                entity_type_id: "Account".into(),
                entity_type_path: vec![],
                entity_id: "buyer".into(),
            },
            agent_id: "root-agent".into(),
            agent_public_key: hex(agent).into(),
            allowed_merchants: vec!["seller".into()],
            allowed_products: vec!["item".into()],
            asset: "HKD".into(),
            per_purchase_cap: 60,
            total_cap: 100,
            policy_epoch: 7,
            expires_at: 30,
        };
        let child = MandatePayload {
            mandate_id: format!("child-{branch}").into(),
            agent_id: format!("agent-{branch}").into(),
            agent_public_key: hex(&simulation_key(branch)).into(),
            total_cap: 60,
            ..root.clone()
        };
        let offer = OfferPayload {
            merchant_id: "seller".into(),
            product_id: "item".into(),
            offer_id: format!("offer-{branch}").into(),
            checkout_sha256: sha256_hex(checkout.as_bytes()),
            amount_minor: 60,
            asset: "HKD".into(),
            expires_at: 25,
        };
        let root_signature: Signature = principal.sign(&root.signing_bytes());
        let child_signature: Signature = agent.sign(&delegation_signing_bytes(&root, &child));
        let offer_signature: Signature = merchant.sign(&offer.signing_bytes());
        let mut trust = MandateOfferTrust::new();
        trust.trust_principal(root.principal.clone(), *principal.verifying_key());
        trust.trust_merchant(offer.merchant_id.clone(), *merchant.verifying_key());
        let verified_root = trust
            .verify_mandate(root.clone(), &root_signature.to_bytes())
            .unwrap();
        let verified_child = trust
            .verify_delegation(&verified_root, child.clone(), &child_signature.to_bytes())
            .unwrap();
        let verified_offer = trust
            .verify_offer(
                offer.clone(),
                checkout.as_bytes(),
                &offer_signature.to_bytes(),
            )
            .unwrap();
        Self {
            root,
            child,
            offer,
            lineage: vec![
                mandate_claims(&verified_root),
                mandate_claims(&verified_child),
            ],
            claims: offer_claims(&verified_offer),
            root_signature: root_signature.to_bytes().into(),
            child_signature: child_signature.to_bytes().into(),
            offer_signature: offer_signature.to_bytes().into(),
            checkout,
        }
    }

    fn steps(&self) -> [SignedDelegation<'_>; 1] {
        [SignedDelegation {
            child: self.child.clone(),
            signature: &self.child_signature,
        }]
    }

    fn use_payment<'a>(
        &'a self,
        host: &'a CommerceAdmissionHost,
        steps: &'a [SignedDelegation<'a>],
    ) -> DelegatedPaymentUse<'a> {
        DelegatedPaymentUse {
            authority: host,
            request: DelegatedAdmissionRequest {
                root: self.root.clone(),
                root_signature: &self.root_signature,
                delegations: steps,
                offer: self.offer.clone(),
                checkout_bytes: self.checkout.as_bytes(),
                offer_signature: &self.offer_signature,
                lean_lineage: &self.lineage,
                lean_offer: &self.claims,
                now: 14,
            },
        }
    }
}

fn hex(key: &SigningKey) -> String {
    key.verifying_key()
        .to_encoded_point(true)
        .as_bytes()
        .iter()
        .map(|value| format!("{value:02x}"))
        .collect()
}

fn payment_simulator(
    name: &str,
    payment: &DelegatedPaymentUse<'_>,
    grant: &crate::gateway::oauth::Grant,
) -> Simulator {
    let mut case = crate::bridge::tests::receipt();
    case.name = name.into();
    case.request.context = json!({"commerceCommitment": payment.commitment().unwrap()});
    let mut schema = (*crate::bridge::tests::validated(case.clone()).schema).clone();
    schema[""]["actions"]["view"]["appliesTo"]["context"]["attributes"]["commerceCommitment"] =
        json!({"type":"String","required":true});
    let schema: SchemaSourceJson = serde_json::from_value(schema).unwrap();
    let simulator =
        Simulator::new_for_oauth(&case, &schema, oauth_current(grant, "configured").target)
            .unwrap();
    simulator.advance_time(14).unwrap();
    simulator
}

#[test]
fn delegated_payment_serializes_charge_and_hold_across_lost_reply_and_takeover() {
    let path = durable_directory("current-payment");
    let receiver_path = durable_directory("current-payment-receiver");
    let successor_path = durable_directory("current-payment-successor");
    let final_path = durable_directory("current-payment-final");
    let receiver_pin = durable_directory("current-payment-pin");
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
        SignedPurchase::new(&principal, &agent, &merchant, 5),
        SignedPurchase::new(&principal, &agent, &merchant, 6),
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
    let steps = [purchases[0].steps(), purchases[1].steps()];
    let simulators = [
        payment_simulator(
            "sibling-a",
            &purchases[0].use_payment(&host, &steps[0]),
            &grant,
        ),
        payment_simulator(
            "sibling-b",
            &purchases[1].use_payment(&host, &steps[1]),
            &grant,
        ),
    ];
    let [(a, a_prepared), (b, b_prepared)] = simulators.each_ref().map(Intent::prepare);
    let calls = [&a, &b];
    let checked = ledger.checkpoint().unwrap();
    let pin = ledger.effect_checkpoint().unwrap();
    let cut = receiver.cut().unwrap();
    let barrier = std::sync::Barrier::new(2);
    let outcomes = std::thread::scope(|scope| {
        let workers: Vec<_> = [a_prepared, b_prepared]
            .into_iter()
            .enumerate()
            .map(|(i, prepared)| {
                let (
                    ledger,
                    receiver,
                    barrier,
                    checked,
                    pin,
                    cut,
                    host,
                    purchases,
                    steps,
                    grant,
                    signer,
                    provider,
                ) = (
                    &ledger, &receiver, &barrier, &checked, &pin, &cut, &host, &purchases, &steps,
                    &grant, &signer, &provider,
                );
                scope.spawn(move || {
                    let call = calls[i];
                    let current = oauth_current(grant, &format!("sibling-{i}"));
                    let dispatch =
                        ReceiverDispatch::sign(cut.clone(), "first", &call.signed, signer).unwrap();
                    let facts = call.audit.facts.accepts(&call.envelope.facts).unwrap();
                    barrier.wait();
                    call.input(
                        prepared,
                        &current,
                        checked,
                        pin,
                        provider.verifying_key(),
                        Some(purchases[i].use_payment(host, &steps[i])),
                    )
                    .mediate(|input, bound| {
                        receiver.receive_oauth_at(
                            ledger,
                            input,
                            ReceiverDelivery {
                                authorization: &dispatch,
                                channel: "first",
                                effect: &call.envelope.effect,
                                bindings: &facts,
                                facts: &call.envelope.facts,
                                publications: &[],
                            },
                            Some(bound),
                            |stage| {
                                if stage == ManagedDeliveryStage::Receiver(CheckpointStage::Durable)
                                {
                                    Err("lost receiver confirmation".into())
                                } else {
                                    Ok(())
                                }
                            },
                        )
                    })
                })
            })
            .collect();
        workers
            .into_iter()
            .map(|worker| worker.join().unwrap())
            .collect::<Vec<_>>()
    });
    let winner = outcomes
        .iter()
        .position(Result::is_err)
        .expect("one durable lost acknowledgment");
    assert_eq!(
        outcomes[winner].as_ref().unwrap_err(),
        "lost receiver confirmation"
    );
    let loser = 1 - winner;
    assert!(outcomes[loser].as_ref().unwrap().is_none());
    assert_eq!(
        ledger.effect_status(&calls[winner].id()).unwrap(),
        EffectStatus::Unresolved
    );
    assert!(receiver.evidence(&calls[loser].id()).unwrap().is_none());
    let before_promotion = receiver.evidence(&calls[winner].id()).unwrap().unwrap();

    let next_writer = ledger.rotate_writer().unwrap();
    let ledger_next = DurableRefreshLedger::new(&path, "authority").for_writer(next_writer);
    let pin0 = receiver.acknowledged_checkpoint().unwrap();
    std::fs::copy(
        receiver_path.join("checkpoint.json"),
        successor_path.join("checkpoint.json"),
    )
    .unwrap();
    let successor = DurableReceiver::managed(
        &successor_path,
        &receiver_pin,
        ReceiverTrust {
            scope: "payments",
            sender: signer.verifying_key(),
            witness: &witness,
            provider: &provider,
        },
    )
    .unwrap();
    successor.promote(&pin0).unwrap();
    assert!(ledger.effect_checkpoint().is_err());
    assert!(receiver.cut().is_err());
    let pin1 = successor.acknowledged_checkpoint().unwrap();
    std::fs::copy(
        successor_path.join("checkpoint.json"),
        final_path.join("checkpoint.json"),
    )
    .unwrap();
    let final_receiver = DurableReceiver::managed(
        &final_path,
        &receiver_pin,
        ReceiverTrust {
            scope: "payments",
            sender: signer.verifying_key(),
            witness: &witness,
            provider: &provider,
        },
    )
    .unwrap();
    let final_writer = ledger_next.rotate_writer().unwrap();
    let ledger_final = ledger.for_writer(final_writer);
    let next_cut = final_receiver.promote(&pin1).unwrap();
    assert!(ledger_next.checkpoint().is_err());
    assert!(successor.cut().is_err());
    let retry = |index: usize, writer: &DurableRefreshLedger<'_>, host: &CommerceAdmissionHost| {
        let (call, prepared) = Intent::prepare(&simulators[index]);
        let current = oauth_current(&grant, "changed-worker");
        let checked = ledger_final.checkpoint().unwrap();
        let pin = ledger_final.effect_checkpoint().unwrap();
        let dispatch =
            ReceiverDispatch::sign(next_cut.clone(), "second", &call.signed, &signer).unwrap();
        let facts = call.audit.facts.accepts(&call.envelope.facts).unwrap();
        let result = final_receiver.receive_current_oauth(
            writer,
            call.input(
                prepared,
                &current,
                &checked,
                &pin,
                provider.verifying_key(),
                Some(purchases[index].use_payment(host, &steps[index])),
            ),
            ReceiverDelivery {
                authorization: &dispatch,
                channel: "second",
                effect: &call.envelope.effect,
                bindings: &facts,
                facts: &call.envelope.facts,
                publications: &[],
            },
        );
        assert!(ledger_final.recover_effects(&pin).unwrap());
        result
    };

    assert!(retry(loser, &ledger, &host).unwrap_err().contains("writer"));
    assert!(
        retry(loser, &ledger_next, &host)
            .unwrap_err()
            .contains("writer")
    );
    assert!(retry(loser, &ledger_final, &host).unwrap().is_none());
    assert!(retry(winner, &ledger_final, &host).unwrap().is_none());
    host.revoke_mandate(
        purchases[0].root.principal.clone(),
        purchases[0].root.mandate_id.clone(),
    );
    assert!(
        retry(loser, &ledger_final, &host)
            .unwrap_err()
            .contains("RevokedMandate")
    );
    assert!(ledger_final.revoke(verified(digest())).unwrap());
    assert!(
        retry(winner, &ledger_final, &host)
            .unwrap_err()
            .contains("RevokedMandate")
    );

    let original = calls[winner];
    let proof = final_receiver.evidence(&original.id()).unwrap().unwrap();
    assert_eq!(proof.outcome.payload, before_promotion.outcome.payload);
    assert_eq!(proof.outcome.signature, before_promotion.outcome.signature);
    let absent = crate::gateway::ProviderJournal::default();
    let recovery = |journal: &crate::gateway::ProviderJournal, outcomes: &[Signed]| {
        final_receiver.reconcile_oauth(
            &ledger_final,
            DurableEffectRecovery {
                effect: &original.envelope.effect,
                journal,
                outcomes,
                history: &original.history,
                trust: ProviderAuditTrust {
                    authority: &original.audit,
                    provider_key: provider.verifying_key(),
                },
            },
        )
    };
    assert!(!recovery(&absent, &[]).unwrap());
    assert_eq!(
        ledger_final.effect_status(&original.id()).unwrap(),
        EffectStatus::Unresolved
    );
    let mut conflicting: crate::gateway::ProviderOutcome =
        crate::gateway::verify(&proof.outcome, provider.verifying_key()).unwrap();
    conflicting.outcome.action.result = "conflicting-result".into();
    let conflicting_journal =
        crate::gateway::ProviderJournal::observation(conflicting.outcome.action.clone());
    let conflicting_signed = crate::gateway::wire::sign(&conflicting, &provider).unwrap();
    assert!(
        !recovery(
            &conflicting_journal,
            std::slice::from_ref(&conflicting_signed)
        )
        .unwrap()
    );
    let recover = || {
        final_receiver.reconcile_oauth(
            &ledger_final,
            DurableEffectRecovery {
                effect: &original.envelope.effect,
                journal: &proof.journal,
                outcomes: std::slice::from_ref(&proof.outcome),
                history: &original.history,
                trust: ProviderAuditTrust {
                    authority: &original.audit,
                    provider_key: provider.verifying_key(),
                },
            },
        )
    };
    assert!(recover().unwrap());
    assert!(recover().unwrap());
    assert!(
        !recovery(
            &conflicting_journal,
            std::slice::from_ref(&conflicting_signed)
        )
        .unwrap()
    );
    assert_eq!(
        ledger_final.effect_status(&original.id()).unwrap(),
        EffectStatus::Reconciled
    );
    assert_eq!(
        ledger_final.effect_status(&calls[loser].id()).unwrap(),
        EffectStatus::Unreserved
    );
    let image: serde_json::Value =
        serde_json::from_slice(&std::fs::read(path.join("checkpoint.json")).unwrap()).unwrap();
    let effects = image["effects"].as_object().unwrap();
    assert_eq!(effects.len(), 1);
    assert_eq!(
        effects[&original.id().0]["purchase_charge"]["terms"]["amountMinor"],
        60
    );
    std::fs::remove_dir_all(path).unwrap();
    std::fs::remove_dir_all(receiver_path).unwrap();
    std::fs::remove_dir_all(successor_path).unwrap();
    std::fs::remove_dir_all(final_path).unwrap();
    std::fs::remove_dir_all(receiver_pin).unwrap();
}

#[derive(serde::Deserialize)]
struct Profile {
    audience: String,
    schema: SchemaSourceJson,
    case: crate::Case,
}

#[test]
#[ignore = "requires the Lean current-commit profiles emitted by RecoveryTraceMain"]
fn lean_current_commit_profiles() {
    let corpus = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/gateway-current-commit-profiles.json");
    let profiles: Vec<Profile> = serde_json::from_slice(&std::fs::read(corpus).unwrap()).unwrap();
    assert_eq!(
        profiles
            .iter()
            .map(|profile| profile.audience.as_str())
            .collect::<Vec<_>>(),
        ["agentcore", "fhir"],
    );
    for (profile, sender) in profiles.into_iter().zip([
        Confirmation::Dpop("agentcore-key".into()),
        Confirmation::Mtls("fhir-certificate".into()),
    ]) {
        assert_eq!(profile.case.expected, "allow");
        let path = durable_directory(&profile.audience);
        let ledger = DurableRefreshLedger::new(&path, "authority");
        ledger.initialize().unwrap();
        let grant = enroll_for_audience(sender, "initial", &profile.audience, |input| {
            ledger.enroll(input).unwrap()
        });
        let simulator = Simulator::new_for_oauth(
            &profile.case,
            &profile.schema,
            oauth_current(&grant, "configured").target,
        )
        .unwrap();
        simulator.advance_time(14).unwrap();
        let (intent, _) = Intent::prepare(&simulator);
        let provider = simulator.provider_verifying_key();
        let checked = ledger.checkpoint().unwrap();
        let pin = ledger.effect_checkpoint().unwrap();
        for mismatch in ["audience", "subject", "uri"] {
            let mut wrong = oauth_current(&grant, "wrong-target");
            match mismatch {
                "audience" => wrong.target.audience = "other-audience".into(),
                "subject" => wrong.target.identity.subject = "other-subject".into(),
                _ => wrong.target.uri = "https://gateway.example/wrong".into(),
            }
            let prepared = simulator.prepare(&intent.envelope).unwrap();
            assert!(
                ledger
                    .execute_current(
                        intent.input(prepared, &wrong, &checked, &pin, &provider, None),
                        |_| panic!("profile admitted the wrong OAuth target"),
                    )
                    .unwrap_err()
                    .contains("witnessed intent differs")
            );
        }
        assert!(ledger.recover_effects(&pin).unwrap());

        let current = oauth_current(&grant, "exact-audience");
        let prepared = simulator.prepare(&intent.envelope).unwrap();
        let input = intent.input(prepared, &current, &checked, &pin, &provider, None);
        let mut bypass = input.authorization;
        bypass.admission.base_allowed = true;
        assert!(
            !ledger
                .execute_effect(bypass, |_| panic!("guarded intent used an unguarded path"),)
                .unwrap()
        );
        let prepared = simulator.prepare(&intent.envelope).unwrap();
        assert!(
            ledger
                .execute_current(
                    intent.input(prepared, &current, &checked, &pin, &provider, None),
                    |_| Ok(()),
                )
                .unwrap()
        );

        assert!(ledger.revoke(verified(digest())).unwrap());
        let mut candidate = profile.case;
        candidate.name.push_str("-after-revocation");
        let simulator = Simulator::new_for_oauth(
            &candidate,
            &profile.schema,
            oauth_current(&grant, "configured").target,
        )
        .unwrap();
        simulator.advance_time(14).unwrap();
        let (attempt, prepared) = Intent::prepare(&simulator);
        let checked = ledger.checkpoint().unwrap();
        let pin = ledger.effect_checkpoint().unwrap();
        let current = oauth_current(&grant, "after-revocation");
        assert!(
            !ledger
                .execute_current(
                    attempt.input(prepared, &current, &checked, &pin, &provider, None),
                    |_| panic!("revoked profile released another effect"),
                )
                .unwrap()
        );
        assert_eq!(
            ledger.effect_status(&attempt.id()).unwrap(),
            EffectStatus::Unreserved
        );
        assert!(ledger.recover_effects(&pin).unwrap());
        eprintln!("CURRENT-COMMIT-PROFILE-OK {}", profile.audience);
        std::fs::remove_dir_all(path).unwrap();
    }
}

#[path = "payment_crash.rs"]
mod payment_crash;
