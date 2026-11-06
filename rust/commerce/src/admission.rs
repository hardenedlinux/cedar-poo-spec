//! Process-local admission reference for signed agentic AI commerce claims.
//!
//! Every call re-verifies signatures and checkout bytes against the Host's
//! current keys before checking time, epoch, revocation, scope, and policy.
//! The deploying Host must authenticate registry updates and its clock, use a
//! real policy evaluator, and recheck these facts when reserving or effecting
//! a purchase. This process-local reference is not a durable authority store.

use crate::projection::{
    LeanMandateClaims, LeanOfferClaims, mandate_claims, mandate_matches, offer_claims,
    offer_matches,
};
use crate::signatures::{
    AgentPublicKey, MandateId, MandateOfferTrust, MandatePayload, MerchantId, OfferId,
    OfferPayload, PrincipalId, VerifiedMandate, VerifiedOffer,
};
use p256::ecdsa::VerifyingKey;
use std::collections::{HashMap, HashSet};

/// A failed check in the process-local admission sequence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AdmissionError {
    InactivePrincipalKey,
    InactiveMerchantKey,
    RevokedAgentKey,
    MandateVerification(String),
    DelegationVerification(String),
    OfferVerification(String),
    MissingDelegation,
    LineageClaimsMismatch,
    MissingPolicyEpoch,
    StalePolicyEpoch,
    PolicyEpochRollback,
    RevokedMandate,
    RevokedOffer,
    ExpiredMandate,
    ExpiredOffer,
    MandateClaimsMismatch,
    OfferClaimsMismatch,
    OutsideMandateScope,
    PolicyDenied,
}

/// Fresh claims for the Host to project into Lean with `verified = true`.
/// A later reservation or external effect needs a fresh state check.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdmittedClaims {
    mandate: LeanMandateClaims,
    offer: LeanOfferClaims,
}

impl AdmittedClaims {
    pub fn mandate(&self) -> &LeanMandateClaims {
        &self.mandate
    }

    pub fn offer(&self) -> &LeanOfferClaims {
        &self.offer
    }
}

/// Exact signed input and Lean claims for one root mandate and merchant offer.
/// The deploying Host must obtain `now` from its own clock.
pub struct AdmissionRequest<'a> {
    pub mandate: MandatePayload,
    pub mandate_signature: &'a [u8],
    pub offer: OfferPayload,
    pub checkout_bytes: &'a [u8],
    pub offer_signature: &'a [u8],
    pub lean_mandate: &'a LeanMandateClaims,
    pub lean_offer: &'a LeanOfferClaims,
    pub now: u64,
}

/// One child mandate signed by the preceding mandate's Agent key.
pub struct SignedDelegation<'a> {
    pub child: MandatePayload,
    pub signature: &'a [u8],
}

/// Complete signed chain and all Lean projections for a delegated admission.
/// The first Lean claim is the root; each following claim matches one child.
pub struct DelegatedAdmissionRequest<'a> {
    pub root: MandatePayload,
    pub root_signature: &'a [u8],
    pub delegations: &'a [SignedDelegation<'a>],
    pub offer: OfferPayload,
    pub checkout_bytes: &'a [u8],
    pub offer_signature: &'a [u8],
    pub lean_lineage: &'a [LeanMandateClaims],
    pub lean_offer: &'a LeanOfferClaims,
    pub now: u64,
}

/// A freshly checked lineage, from principal-signed root to final child.
/// Every node needs fresh Host state checks again at reservation or effect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdmittedDelegation {
    lineage: Vec<LeanMandateClaims>,
    offer: LeanOfferClaims,
}

impl AdmittedDelegation {
    pub fn lineage(&self) -> &[LeanMandateClaims] {
        &self.lineage
    }

    pub fn offer(&self) -> &LeanOfferClaims {
        &self.offer
    }
}

/// Accounting evidence retained with an already reserved operation.
/// Restoring this value does not authenticate a new mandate or offer.
#[derive(Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PurchaseCharge {
    lineage: Vec<LeanMandateClaims>,
    terms: crate::projection::LeanPurchaseTermsClaims,
}

impl AdmittedDelegation {
    /// Compute one charge from current verified claims and retained prior charges.
    /// The caller serializes this calculation with operation reservation and commit.
    pub fn charge<'a>(
        &self,
        prior: impl IntoIterator<Item = &'a PurchaseCharge>,
    ) -> Option<PurchaseCharge> {
        let root = self.lineage.first()?;
        let mut spent = vec![0u64; self.lineage.len()];
        for row in prior {
            let old_root = row.lineage.first()?;
            if old_root.principal != root.principal || old_root.mandate_id != root.mandate_id {
                continue;
            }
            if old_root != root
                || (row.terms.merchant_id == self.offer.terms.merchant_id
                    && row.terms.offer_id == self.offer.terms.offer_id)
            {
                return None;
            }
            for (ancestor, total) in self.lineage.iter().zip(&mut spent) {
                if let Some(old) = row
                    .lineage
                    .iter()
                    .find(|m| m.mandate_id == ancestor.mandate_id)
                {
                    if old != ancestor {
                        return None;
                    }
                    *total = total.checked_add(row.terms.amount_minor)?;
                }
            }
        }
        for (ancestor, total) in self.lineage.iter().zip(spent) {
            if total.checked_add(self.offer.terms.amount_minor)? > ancestor.total_cap {
                return None;
            }
        }
        Some(PurchaseCharge {
            lineage: self.lineage.clone(),
            terms: self.offer.terms.clone(),
        })
    }
}

/// Host-controlled, process-local admission state. The key sets track current
/// active status; re-enrollment rotates a key and old signatures fail on use.
#[derive(Default)]
pub struct CommerceAdmissionHost {
    trust: MandateOfferTrust,
    active_principals: HashSet<PrincipalId>,
    active_merchants: HashSet<MerchantId>,
    revoked_agent_keys: HashSet<AgentPublicKey>,
    policy_epochs: HashMap<PrincipalId, u64>,
    revoked_mandates: HashSet<(PrincipalId, MandateId)>,
    revoked_offers: HashSet<(MerchantId, OfferId)>,
}

impl CommerceAdmissionHost {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn enroll_principal_key(&mut self, principal: PrincipalId, key: VerifyingKey) {
        self.trust.trust_principal(principal.clone(), key);
        self.active_principals.insert(principal);
    }

    pub fn enroll_merchant_key(&mut self, merchant: MerchantId, key: VerifyingKey) {
        self.trust.trust_merchant(merchant.clone(), key);
        self.active_merchants.insert(merchant);
    }

    pub fn deactivate_principal_key(&mut self, principal: &PrincipalId) {
        self.active_principals.remove(principal);
    }

    pub fn deactivate_merchant_key(&mut self, merchant: &MerchantId) {
        self.active_merchants.remove(merchant);
    }

    /// Reject this Agent key as a current delegate or holder of authority.
    pub fn revoke_agent_key(&mut self, key: AgentPublicKey) {
        self.revoked_agent_keys.insert(key);
    }

    /// The current epoch is exact. Lower values cannot reopen old authority.
    pub fn set_policy_epoch(
        &mut self,
        principal: PrincipalId,
        epoch: u64,
    ) -> Result<(), AdmissionError> {
        if self
            .policy_epochs
            .get(&principal)
            .is_some_and(|current| epoch < *current)
        {
            return Err(AdmissionError::PolicyEpochRollback);
        }
        self.policy_epochs.insert(principal, epoch);
        Ok(())
    }

    pub fn revoke_mandate(&mut self, principal: PrincipalId, mandate: MandateId) {
        self.revoked_mandates.insert((principal, mandate));
    }

    pub fn revoke_offer(&mut self, merchant: MerchantId, offer: OfferId) {
        self.revoked_offers.insert((merchant, offer));
    }

    /// Re-verify signed root evidence and current Host state before projecting
    /// claims. `policy_allows` must evaluate current policy over these claims.
    pub fn admit<F>(
        &self,
        request: AdmissionRequest<'_>,
        policy_allows: F,
    ) -> Result<AdmittedClaims, AdmissionError>
    where
        F: FnOnce(&LeanMandateClaims, &LeanOfferClaims) -> bool,
    {
        let (verified_mandate, verified_offer) = self.verify_signatures(&request)?;
        self.check_current_state(&verified_mandate, &verified_offer, request.now)?;
        Self::check_claims_and_scope(&verified_mandate, &verified_offer, &request)?;
        if !policy_allows(request.lean_mandate, request.lean_offer) {
            return Err(AdmissionError::PolicyDenied);
        }
        Ok(AdmittedClaims {
            mandate: mandate_claims(&verified_mandate),
            offer: offer_claims(&verified_offer),
        })
    }

    /// Rebuild the complete chain from signed bytes against current Host state.
    /// Policy sees every exact verified mandate, including the root.
    pub fn admit_delegated<F>(
        &self,
        request: DelegatedAdmissionRequest<'_>,
        policy_allows: F,
    ) -> Result<AdmittedDelegation, AdmissionError>
    where
        F: FnOnce(&[LeanMandateClaims], &LeanOfferClaims) -> bool,
    {
        let (verified, lineage) = self.verify_lineage(&request)?;
        let offer = self.verify_delegated_offer(&request)?;
        let offer_claims = offer_claims(&offer);
        if lineage != request.lean_lineage || offer_claims != *request.lean_offer {
            return Err(AdmissionError::LineageClaimsMismatch);
        }
        Self::check_scope(verified.payload(), offer.payload())?;
        if !policy_allows(&lineage, &offer_claims) {
            return Err(AdmissionError::PolicyDenied);
        }
        Ok(AdmittedDelegation {
            lineage,
            offer: offer_claims,
        })
    }

    fn verify_lineage(
        &self,
        request: &DelegatedAdmissionRequest<'_>,
    ) -> Result<(VerifiedMandate, Vec<LeanMandateClaims>), AdmissionError> {
        if request.delegations.is_empty() {
            return Err(AdmissionError::MissingDelegation);
        }
        if !self.active_principals.contains(&request.root.principal) {
            return Err(AdmissionError::InactivePrincipalKey);
        }
        let mut verified = self
            .trust
            .verify_mandate(request.root.clone(), request.root_signature)
            .map_err(AdmissionError::MandateVerification)?;
        self.check_mandate_state(verified.payload(), request.now)?;
        let mut lineage = vec![mandate_claims(&verified)];
        for delegation in request.delegations {
            let child = self
                .trust
                .verify_delegation(&verified, delegation.child.clone(), delegation.signature)
                .map_err(AdmissionError::DelegationVerification)?;
            self.check_mandate_state(child.payload(), request.now)?;
            lineage.push(mandate_claims(&child));
            verified = child;
        }
        Ok((verified, lineage))
    }

    fn verify_delegated_offer(
        &self,
        request: &DelegatedAdmissionRequest<'_>,
    ) -> Result<VerifiedOffer, AdmissionError> {
        if !self.active_merchants.contains(&request.offer.merchant_id) {
            return Err(AdmissionError::InactiveMerchantKey);
        }
        let offer = self
            .trust
            .verify_offer(
                request.offer.clone(),
                request.checkout_bytes,
                request.offer_signature,
            )
            .map_err(AdmissionError::OfferVerification)?;
        self.check_offer_state(offer.payload(), request.now)?;
        Ok(offer)
    }

    fn verify_signatures(
        &self,
        request: &AdmissionRequest<'_>,
    ) -> Result<(VerifiedMandate, VerifiedOffer), AdmissionError> {
        if !self.active_principals.contains(&request.mandate.principal) {
            return Err(AdmissionError::InactivePrincipalKey);
        }
        if !self.active_merchants.contains(&request.offer.merchant_id) {
            return Err(AdmissionError::InactiveMerchantKey);
        }
        let verified_mandate = self
            .trust
            .verify_mandate(request.mandate.clone(), request.mandate_signature)
            .map_err(AdmissionError::MandateVerification)?;
        let verified_offer = self
            .trust
            .verify_offer(
                request.offer.clone(),
                request.checkout_bytes,
                request.offer_signature,
            )
            .map_err(AdmissionError::OfferVerification)?;
        Ok((verified_mandate, verified_offer))
    }

    fn check_current_state(
        &self,
        verified_mandate: &VerifiedMandate,
        verified_offer: &VerifiedOffer,
        now: u64,
    ) -> Result<(), AdmissionError> {
        self.check_mandate_state(verified_mandate.payload(), now)?;
        self.check_offer_state(verified_offer.payload(), now)
    }

    fn check_mandate_state(
        &self,
        mandate: &MandatePayload,
        now: u64,
    ) -> Result<(), AdmissionError> {
        match self.policy_epochs.get(&mandate.principal) {
            None => return Err(AdmissionError::MissingPolicyEpoch),
            Some(epoch) if *epoch != mandate.policy_epoch => {
                return Err(AdmissionError::StalePolicyEpoch);
            }
            Some(_) => {}
        }
        if self
            .revoked_mandates
            .contains(&(mandate.principal.clone(), mandate.mandate_id.clone()))
        {
            return Err(AdmissionError::RevokedMandate);
        }
        if self.revoked_agent_keys.contains(&mandate.agent_public_key) {
            return Err(AdmissionError::RevokedAgentKey);
        }
        if now >= mandate.expires_at {
            return Err(AdmissionError::ExpiredMandate);
        }
        Ok(())
    }

    fn check_offer_state(&self, offer: &OfferPayload, now: u64) -> Result<(), AdmissionError> {
        if self
            .revoked_offers
            .contains(&(offer.merchant_id.clone(), offer.offer_id.clone()))
        {
            return Err(AdmissionError::RevokedOffer);
        }
        if now >= offer.expires_at {
            return Err(AdmissionError::ExpiredOffer);
        }
        Ok(())
    }

    fn check_claims_and_scope(
        verified_mandate: &VerifiedMandate,
        verified_offer: &VerifiedOffer,
        request: &AdmissionRequest<'_>,
    ) -> Result<(), AdmissionError> {
        let mandate = verified_mandate.payload();
        let offer = verified_offer.payload();
        if !mandate_matches(verified_mandate, request.lean_mandate) {
            return Err(AdmissionError::MandateClaimsMismatch);
        }
        if !offer_matches(verified_offer, request.lean_offer) {
            return Err(AdmissionError::OfferClaimsMismatch);
        }
        Self::check_scope(mandate, offer)
    }

    fn check_scope(mandate: &MandatePayload, offer: &OfferPayload) -> Result<(), AdmissionError> {
        if !mandate.allowed_merchants.contains(&offer.merchant_id)
            || !mandate.allowed_products.contains(&offer.product_id)
            || mandate.asset != offer.asset
            || offer.amount_minor > mandate.per_purchase_cap
        {
            return Err(AdmissionError::OutsideMandateScope);
        }
        Ok(())
    }
}
