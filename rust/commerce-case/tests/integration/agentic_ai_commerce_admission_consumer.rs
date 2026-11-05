use cedar_poo_commerce::admission::{
    AdmissionError, AdmissionRequest, CommerceAdmissionHost, DelegatedAdmissionRequest,
    SignedDelegation,
};
use cedar_poo_commerce::projection::{
    LeanMandateClaims, LeanOfferClaims, mandate_claims, offer_claims,
};
use cedar_poo_commerce::signatures::{
    MandateOfferTrust, MandatePayload, OfferPayload, PrincipalId, delegation_signing_bytes,
    sha256_hex,
};
use p256::ecdsa::{Signature, SigningKey, signature::Signer};

fn signer(seed: u8) -> SigningKey {
    SigningKey::from_bytes((&[seed; 32]).into()).expect("test key")
}

fn key_hex(key: &SigningKey) -> String {
    key.verifying_key()
        .to_encoded_point(true)
        .as_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

struct Fixture {
    principal_key: SigningKey,
    agent_key: SigningKey,
    merchant_key: SigningKey,
    mandate: MandatePayload,
    offer: OfferPayload,
    checkout: Vec<u8>,
}

impl Fixture {
    fn new() -> Self {
        let principal_key = signer(1);
        let agent_key = signer(2);
        let agent_public_key = key_hex(&agent_key);
        let merchant_key = signer(3);
        let checkout = br#"{"ride":"airport","total_minor":30000}"#.to_vec();
        Self {
            principal_key,
            agent_key,
            merchant_key,
            mandate: MandatePayload {
                mandate_id: "trip-root".into(),
                principal: PrincipalId {
                    entity_type_id: "Account".into(),
                    entity_type_path: vec!["finance".into()],
                    entity_id: "buyer".into(),
                },
                agent_id: "travel-agent".into(),
                agent_public_key: agent_public_key.into(),
                allowed_merchants: vec!["ride-seller".into()],
                allowed_products: vec!["airport-ride".into()],
                asset: "HKD".into(),
                per_purchase_cap: 50_000,
                total_cap: 80_000,
                policy_epoch: 4,
                expires_at: 30,
            },
            offer: OfferPayload {
                merchant_id: "ride-seller".into(),
                product_id: "airport-ride".into(),
                offer_id: "quote-42".into(),
                checkout_sha256: sha256_hex(&checkout),
                amount_minor: 30_000,
                asset: "HKD".into(),
                expires_at: 20,
            },
            checkout,
        }
    }

    fn trust(&self) -> MandateOfferTrust {
        let mut trust = MandateOfferTrust::new();
        trust.trust_principal(
            self.mandate.principal.clone(),
            *self.principal_key.verifying_key(),
        );
        trust.trust_merchant(
            self.offer.merchant_id.clone(),
            *self.merchant_key.verifying_key(),
        );
        trust
    }

    fn host(&self) -> CommerceAdmissionHost {
        let mut host = CommerceAdmissionHost::new();
        host.enroll_principal_key(
            self.mandate.principal.clone(),
            *self.principal_key.verifying_key(),
        );
        host.enroll_merchant_key(
            self.offer.merchant_id.clone(),
            *self.merchant_key.verifying_key(),
        );
        host.set_policy_epoch(self.mandate.principal.clone(), 4)
            .unwrap();
        host
    }

    fn claims(&self) -> (LeanMandateClaims, LeanOfferClaims) {
        let trust = self.trust();
        let mandate_signature: Signature = self.principal_key.sign(&self.mandate.signing_bytes());
        let offer_signature: Signature = self.merchant_key.sign(&self.offer.signing_bytes());
        let mandate = trust
            .verify_mandate(
                self.mandate.clone(),
                mandate_signature.to_bytes().as_slice(),
            )
            .unwrap();
        let offer = trust
            .verify_offer(
                self.offer.clone(),
                &self.checkout,
                offer_signature.to_bytes().as_slice(),
            )
            .unwrap();
        (mandate_claims(&mandate), offer_claims(&offer))
    }

    fn admit(
        &self,
        host: &CommerceAdmissionHost,
        claims: (&LeanMandateClaims, &LeanOfferClaims),
        now: u64,
        policy_allows: bool,
    ) -> Result<cedar_poo_commerce::admission::AdmittedClaims, AdmissionError> {
        let mandate_signature: Signature = self.principal_key.sign(&self.mandate.signing_bytes());
        let offer_signature: Signature = self.merchant_key.sign(&self.offer.signing_bytes());
        host.admit(
            AdmissionRequest {
                mandate: self.mandate.clone(),
                mandate_signature: mandate_signature.to_bytes().as_slice(),
                offer: self.offer.clone(),
                checkout_bytes: &self.checkout,
                offer_signature: offer_signature.to_bytes().as_slice(),
                lean_mandate: claims.0,
                lean_offer: claims.1,
                now,
            },
            |_, _| policy_allows,
        )
    }
}

struct DelegatedFixture {
    root: Fixture,
    child: MandatePayload,
}

impl DelegatedFixture {
    fn new() -> Self {
        let root = Fixture::new();
        let child_key = signer(4);
        let child = MandatePayload {
            mandate_id: "trip-child".into(),
            agent_id: "booking-agent".into(),
            agent_public_key: key_hex(&child_key).into(),
            per_purchase_cap: 40_000,
            total_cap: 60_000,
            expires_at: 25,
            ..root.mandate.clone()
        };
        Self { root, child }
    }

    fn claims(&self) -> (Vec<LeanMandateClaims>, LeanOfferClaims) {
        let trust = self.root.trust();
        let root_signature: Signature = self
            .root
            .principal_key
            .sign(&self.root.mandate.signing_bytes());
        let root = trust
            .verify_mandate(
                self.root.mandate.clone(),
                root_signature.to_bytes().as_slice(),
            )
            .unwrap();
        let child_signature: Signature = self
            .root
            .agent_key
            .sign(&delegation_signing_bytes(&self.root.mandate, &self.child));
        let child = trust
            .verify_delegation(
                &root,
                self.child.clone(),
                child_signature.to_bytes().as_slice(),
            )
            .unwrap();
        let offer_signature: Signature = self
            .root
            .merchant_key
            .sign(&self.root.offer.signing_bytes());
        let offer = trust
            .verify_offer(
                self.root.offer.clone(),
                &self.root.checkout,
                offer_signature.to_bytes().as_slice(),
            )
            .unwrap();
        (
            vec![mandate_claims(&root), mandate_claims(&child)],
            offer_claims(&offer),
        )
    }

    fn admit(
        &self,
        host: &CommerceAdmissionHost,
        lineage: &[LeanMandateClaims],
        offer: &LeanOfferClaims,
    ) -> Result<cedar_poo_commerce::admission::AdmittedDelegation, AdmissionError> {
        self.admit_with_policy(host, lineage, offer, |claims, actual_offer| {
            claims == lineage && actual_offer == offer
        })
    }

    fn admit_with_policy<F>(
        &self,
        host: &CommerceAdmissionHost,
        lineage: &[LeanMandateClaims],
        offer: &LeanOfferClaims,
        policy_allows: F,
    ) -> Result<cedar_poo_commerce::admission::AdmittedDelegation, AdmissionError>
    where
        F: FnOnce(&[LeanMandateClaims], &LeanOfferClaims) -> bool,
    {
        let root_signature: Signature = self
            .root
            .principal_key
            .sign(&self.root.mandate.signing_bytes());
        let child_signature: Signature = self
            .root
            .agent_key
            .sign(&delegation_signing_bytes(&self.root.mandate, &self.child));
        let offer_signature: Signature = self
            .root
            .merchant_key
            .sign(&self.root.offer.signing_bytes());
        let child_signature_bytes = child_signature.to_bytes();
        let delegations = [SignedDelegation {
            child: self.child.clone(),
            signature: child_signature_bytes.as_slice(),
        }];
        host.admit_delegated(
            DelegatedAdmissionRequest {
                root: self.root.mandate.clone(),
                root_signature: root_signature.to_bytes().as_slice(),
                delegations: &delegations,
                offer: self.root.offer.clone(),
                checkout_bytes: &self.root.checkout,
                offer_signature: offer_signature.to_bytes().as_slice(),
                lean_lineage: lineage,
                lean_offer: offer,
                now: 10,
            },
            policy_allows,
        )
    }
}

#[test]
fn fresh_signed_claims_admit_and_policy_denial_blocks() {
    let fixture = Fixture::new();
    let host = fixture.host();
    let (mandate, offer) = fixture.claims();
    let admitted = fixture.admit(&host, (&mandate, &offer), 10, true).unwrap();
    assert_eq!(admitted.mandate(), &mandate);
    assert_eq!(admitted.offer(), &offer);
    assert_eq!(
        fixture.admit(&host, (&mandate, &offer), 10, false),
        Err(AdmissionError::PolicyDenied)
    );
    let mut changed = mandate.clone();
    changed.agent_id = "other-agent".into();
    assert_eq!(
        fixture.admit(&host, (&changed, &offer), 10, true),
        Err(AdmissionError::MandateClaimsMismatch)
    );
    let mut changed_offer = offer.clone();
    changed_offer.terms.amount_minor += 1;
    assert_eq!(
        fixture.admit(&host, (&mandate, &changed_offer), 10, true),
        Err(AdmissionError::OfferClaimsMismatch)
    );
}

#[test]
fn expiry_and_current_epoch_are_rechecked_at_admission() {
    let fixture = Fixture::new();
    let mut host = fixture.host();
    let (mandate, offer) = fixture.claims();
    assert_eq!(
        fixture.admit(&host, (&mandate, &offer), 20, true),
        Err(AdmissionError::ExpiredOffer)
    );
    assert_eq!(
        fixture.admit(&host, (&mandate, &offer), 30, true),
        Err(AdmissionError::ExpiredMandate)
    );
    host.set_policy_epoch(fixture.mandate.principal.clone(), 5)
        .unwrap();
    assert_eq!(
        fixture.admit(&host, (&mandate, &offer), 10, true),
        Err(AdmissionError::StalePolicyEpoch)
    );
    assert_eq!(
        host.set_policy_epoch(fixture.mandate.principal.clone(), 4),
        Err(AdmissionError::PolicyEpochRollback)
    );
    let mut missing_epoch = CommerceAdmissionHost::new();
    missing_epoch.enroll_principal_key(
        fixture.mandate.principal.clone(),
        *fixture.principal_key.verifying_key(),
    );
    missing_epoch.enroll_merchant_key(
        fixture.offer.merchant_id.clone(),
        *fixture.merchant_key.verifying_key(),
    );
    assert_eq!(
        fixture.admit(&missing_epoch, (&mandate, &offer), 10, true),
        Err(AdmissionError::MissingPolicyEpoch)
    );
}

#[test]
fn key_rotation_and_revocation_invalidate_old_signed_evidence() {
    let fixture = Fixture::new();
    let (mandate, offer) = fixture.claims();
    let mut host = fixture.host();
    assert!(fixture.admit(&host, (&mandate, &offer), 10, true).is_ok());
    host.deactivate_principal_key(&fixture.mandate.principal);
    assert_eq!(
        fixture.admit(&host, (&mandate, &offer), 10, true),
        Err(AdmissionError::InactivePrincipalKey)
    );
    host.enroll_principal_key(
        fixture.mandate.principal.clone(),
        *signer(4).verifying_key(),
    );
    assert!(matches!(
        fixture.admit(&host, (&mandate, &offer), 10, true),
        Err(AdmissionError::MandateVerification(_))
    ));
    host.enroll_principal_key(
        fixture.mandate.principal.clone(),
        *fixture.principal_key.verifying_key(),
    );
    host.deactivate_merchant_key(&fixture.offer.merchant_id);
    assert_eq!(
        fixture.admit(&host, (&mandate, &offer), 10, true),
        Err(AdmissionError::InactiveMerchantKey)
    );
    host.enroll_merchant_key(
        fixture.offer.merchant_id.clone(),
        *signer(5).verifying_key(),
    );
    assert!(matches!(
        fixture.admit(&host, (&mandate, &offer), 10, true),
        Err(AdmissionError::OfferVerification(_))
    ));
    host.enroll_merchant_key(
        fixture.offer.merchant_id.clone(),
        *fixture.merchant_key.verifying_key(),
    );
    host.revoke_mandate(
        fixture.mandate.principal.clone(),
        fixture.mandate.mandate_id.clone(),
    );
    assert_eq!(
        fixture.admit(&host, (&mandate, &offer), 10, true),
        Err(AdmissionError::RevokedMandate)
    );
    let mut other = fixture.host();
    other.revoke_offer(
        fixture.offer.merchant_id.clone(),
        fixture.offer.offer_id.clone(),
    );
    assert_eq!(
        fixture.admit(&other, (&mandate, &offer), 10, true),
        Err(AdmissionError::RevokedOffer)
    );
}

#[test]
fn verified_offer_outside_mandate_scope_still_denied() {
    let mut fixture = Fixture::new();
    fixture.offer.amount_minor = 50_001;
    let (mandate, offer) = fixture.claims();
    let host = fixture.host();
    assert_eq!(
        fixture.admit(&host, (&mandate, &offer), 10, true),
        Err(AdmissionError::OutsideMandateScope)
    );
}

#[test]
fn changed_checkout_fails_before_policy_evaluation() {
    let fixture = Fixture::new();
    let (mandate, offer) = fixture.claims();
    let host = fixture.host();
    let mandate_signature: Signature = fixture.principal_key.sign(&fixture.mandate.signing_bytes());
    let offer_signature: Signature = fixture.merchant_key.sign(&fixture.offer.signing_bytes());
    let mut policy_called = false;
    let result = host.admit(
        AdmissionRequest {
            mandate: fixture.mandate.clone(),
            mandate_signature: mandate_signature.to_bytes().as_slice(),
            offer: fixture.offer.clone(),
            checkout_bytes: b"changed checkout bytes",
            offer_signature: offer_signature.to_bytes().as_slice(),
            lean_mandate: &mandate,
            lean_offer: &offer,
            now: 10,
        },
        |_, _| {
            policy_called = true;
            true
        },
    );
    assert!(matches!(result, Err(AdmissionError::OfferVerification(_))));
    assert!(!policy_called);
}

#[test]
fn delegated_admission_rechecks_root_child_and_exact_lineage() {
    let fixture = DelegatedFixture::new();
    let (lineage, offer) = fixture.claims();
    let host = fixture.root.host();
    let admitted = fixture.admit(&host, &lineage, &offer).unwrap();
    assert_eq!(admitted.lineage(), lineage);
    assert_eq!(admitted.offer(), &offer);

    let mut changed = lineage.clone();
    changed[0].principal.eid = "other".into();
    assert_eq!(
        fixture.admit(&host, &changed, &offer),
        Err(AdmissionError::LineageClaimsMismatch)
    );
    let mut changed = lineage.clone();
    changed[1].per_purchase_cap += 1;
    assert_eq!(
        fixture.admit(&host, &changed, &offer),
        Err(AdmissionError::LineageClaimsMismatch)
    );
    assert_eq!(
        fixture.admit(&host, &lineage[..1], &offer),
        Err(AdmissionError::LineageClaimsMismatch)
    );
    let mut changed_offer = offer.clone();
    changed_offer.terms.amount_minor += 1;
    assert_eq!(
        fixture.admit(&host, &lineage, &changed_offer),
        Err(AdmissionError::LineageClaimsMismatch)
    );
}

#[test]
fn ancestor_and_agent_revocation_reject_old_delegation_chain() {
    let fixture = DelegatedFixture::new();
    let (lineage, offer) = fixture.claims();
    let mut host = fixture.root.host();
    host.revoke_mandate(
        fixture.root.mandate.principal.clone(),
        fixture.root.mandate.mandate_id.clone(),
    );
    assert_eq!(
        fixture.admit(&host, &lineage, &offer),
        Err(AdmissionError::RevokedMandate)
    );

    let mut host = fixture.root.host();
    host.revoke_agent_key(fixture.root.mandate.agent_public_key.clone());
    assert_eq!(
        fixture.admit(&host, &lineage, &offer),
        Err(AdmissionError::RevokedAgentKey)
    );

    let mut host = fixture.root.host();
    host.revoke_mandate(
        fixture.child.principal.clone(),
        fixture.child.mandate_id.clone(),
    );
    assert_eq!(
        fixture.admit(&host, &lineage, &offer),
        Err(AdmissionError::RevokedMandate)
    );

    let mut host = fixture.root.host();
    host.revoke_agent_key(fixture.child.agent_public_key.clone());
    assert_eq!(
        fixture.admit(&host, &lineage, &offer),
        Err(AdmissionError::RevokedAgentKey)
    );

    let mut host = fixture.root.host();
    host.enroll_principal_key(
        fixture.root.mandate.principal.clone(),
        *signer(9).verifying_key(),
    );
    assert!(matches!(
        fixture.admit(&host, &lineage, &offer),
        Err(AdmissionError::MandateVerification(_))
    ));
}

#[test]
fn delegated_policy_runs_only_after_current_chain_and_claims() {
    let fixture = DelegatedFixture::new();
    let (lineage, offer) = fixture.claims();
    let mut host = fixture.root.host();
    host.revoke_agent_key(fixture.root.mandate.agent_public_key.clone());
    let mut called = false;
    let result = fixture.admit_with_policy(&host, &lineage, &offer, |_, _| {
        called = true;
        true
    });
    assert_eq!(result, Err(AdmissionError::RevokedAgentKey));
    assert!(!called);

    let host = fixture.root.host();
    let mut changed = lineage.clone();
    changed[1].agent_id = "other".into();
    let result = fixture.admit_with_policy(&host, &changed, &offer, |_, _| {
        called = true;
        true
    });
    assert_eq!(result, Err(AdmissionError::LineageClaimsMismatch));
    assert!(!called);

    let result = fixture.admit_with_policy(&host, &lineage, &offer, |_, _| {
        called = true;
        false
    });
    assert_eq!(result, Err(AdmissionError::PolicyDenied));
    assert!(called);
}

#[test]
fn two_hop_admission_rechecks_intermediate_mandate() {
    let fixture = DelegatedFixture::new();
    let (mut lineage, offer_claims) = fixture.claims();
    let grandchild = MandatePayload {
        mandate_id: "trip-grandchild".into(),
        agent_id: "checkout-agent".into(),
        agent_public_key: key_hex(&signer(5)).into(),
        per_purchase_cap: 30_000,
        total_cap: 50_000,
        expires_at: 20,
        ..fixture.child.clone()
    };
    let root_signature: Signature = fixture
        .root
        .principal_key
        .sign(&fixture.root.mandate.signing_bytes());
    let child_signature: Signature = fixture.root.agent_key.sign(&delegation_signing_bytes(
        &fixture.root.mandate,
        &fixture.child,
    ));
    let grandchild_signature: Signature =
        signer(4).sign(&delegation_signing_bytes(&fixture.child, &grandchild));
    let offer_signature: Signature = fixture
        .root
        .merchant_key
        .sign(&fixture.root.offer.signing_bytes());
    let child_signature_bytes = child_signature.to_bytes();
    let grandchild_signature_bytes = grandchild_signature.to_bytes();
    let delegations = [
        SignedDelegation {
            child: fixture.child.clone(),
            signature: child_signature_bytes.as_slice(),
        },
        SignedDelegation {
            child: grandchild.clone(),
            signature: grandchild_signature_bytes.as_slice(),
        },
    ];
    let root = fixture
        .root
        .trust()
        .verify_mandate(
            fixture.root.mandate.clone(),
            root_signature.to_bytes().as_slice(),
        )
        .unwrap();
    let child = fixture
        .root
        .trust()
        .verify_delegation(
            &root,
            fixture.child.clone(),
            child_signature_bytes.as_slice(),
        )
        .unwrap();
    let final_mandate = fixture
        .root
        .trust()
        .verify_delegation(&child, grandchild, grandchild_signature_bytes.as_slice())
        .unwrap();
    lineage.push(mandate_claims(&final_mandate));
    let admit = |host: &CommerceAdmissionHost| {
        host.admit_delegated(
            DelegatedAdmissionRequest {
                root: fixture.root.mandate.clone(),
                root_signature: root_signature.to_bytes().as_slice(),
                delegations: &delegations,
                offer: fixture.root.offer.clone(),
                checkout_bytes: &fixture.root.checkout,
                offer_signature: offer_signature.to_bytes().as_slice(),
                lean_lineage: &lineage,
                lean_offer: &offer_claims,
                now: 10,
            },
            |claims, _| claims.len() == 3,
        )
    };
    let mut host = fixture.root.host();
    assert_eq!(admit(&host).unwrap().lineage(), lineage);
    host.revoke_mandate(
        fixture.child.principal.clone(),
        fixture.child.mandate_id.clone(),
    );
    assert_eq!(admit(&host), Err(AdmissionError::RevokedMandate));
}

#[test]
fn delegated_admission_rejects_nonadjacent_identity_reuse() {
    // Each child is signed by its immediate parent. Only the complete
    // lineage reveals reuse of the root or an earlier non-root identity.
    for ancestor in [0usize, 1] {
        for reused_field in ["none", "mandate", "agent", "key"] {
            let fixture = DelegatedFixture::new();
            let mut mandates = vec![fixture.root.mandate.clone(), fixture.child.clone()];
            let keys = [signer(2), signer(4), signer(5), signer(6)];
            for index in 2..=3 {
                mandates.push(MandatePayload {
                    mandate_id: format!("descendant-{index}").into(),
                    agent_id: format!("agent-{index}").into(),
                    agent_public_key: key_hex(&keys[index]).into(),
                    ..mandates[index - 1].clone()
                });
            }
            let prior = mandates[ancestor].clone();
            match reused_field {
                "mandate" => mandates[3].mandate_id = prior.mandate_id,
                "agent" => mandates[3].agent_id = prior.agent_id,
                "key" => mandates[3].agent_public_key = prior.agent_public_key,
                _ => {}
            }
            let root_signature: Signature = fixture
                .root
                .principal_key
                .sign(&mandates[0].signing_bytes());
            let (mut lineage, offer) = fixture.claims();
            for mandate in &mandates[2..] {
                let mut claims = lineage[1].clone();
                claims.mandate_id = mandate.mandate_id.clone();
                claims.agent_id = mandate.agent_id.clone();
                claims.agent_public_key = mandate.agent_public_key.clone();
                lineage.push(claims);
            }
            let signatures: Vec<Signature> = mandates
                .windows(2)
                .enumerate()
                .map(|(index, pair)| {
                    keys[index].sign(&delegation_signing_bytes(&pair[0], &pair[1]))
                })
                .collect();
            let signature_bytes: Vec<_> = signatures.iter().map(Signature::to_bytes).collect();
            let delegations: Vec<_> = mandates[1..]
                .iter()
                .zip(&signature_bytes)
                .map(|(child, signature)| SignedDelegation {
                    child: child.clone(),
                    signature: signature.as_slice(),
                })
                .collect();
            let offer_signature: Signature = fixture
                .root
                .merchant_key
                .sign(&fixture.root.offer.signing_bytes());
            let host = fixture.root.host();
            let mut policy_called = false;
            let result = host.admit_delegated(
                DelegatedAdmissionRequest {
                    root: mandates[0].clone(),
                    root_signature: root_signature.to_bytes().as_slice(),
                    delegations: &delegations,
                    offer: fixture.root.offer.clone(),
                    checkout_bytes: &fixture.root.checkout,
                    offer_signature: offer_signature.to_bytes().as_slice(),
                    lean_lineage: &lineage,
                    lean_offer: &offer,
                    now: 10,
                },
                |actual, actual_offer| {
                    policy_called = true;
                    actual == lineage && actual_offer == &offer
                },
            );
            if reused_field == "none" {
                assert!(result.is_ok(), "{result:?}");
                assert!(policy_called);
            } else {
                assert!(
                    matches!(result, Err(AdmissionError::DelegationVerification(_))),
                    "accepted repeated {reused_field} from ancestor {ancestor}: {result:?}"
                );
                assert!(!policy_called);
            }
        }
    }
}
