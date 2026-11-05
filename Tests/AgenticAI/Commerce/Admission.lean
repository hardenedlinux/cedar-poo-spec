import CedarPooSpec.Vertical.FinancialServices.AgenticCommercePayment
import CedarPooSpec.AgenticAI.Commerce.SharedBudget
import Examples.Enterprise.Agent.Payment.AgentPayment

namespace CedarPooSpec.AgenticAI.CommerceTest

open CedarPooSpec.Vertical.FinancialServices
open CedarPooSpec.AgenticAI.Commerce
open CedarPooSpec.AgentDelegationExample
open CedarPooSpec.AgentPaymentExample

def mandate : Mandate :=
  { mandateId := "trip-2026", principal := approvedAccount,
    agentId := "travel-agent-7", agentPublicKey := "agent-key-7",
    allowedMerchants := ["ride-provider"],
    allowedProducts := ["airport-ride"], asset := "HKD",
    perPurchaseCap := 50000, totalCap := 80000,
    policyEpoch := 4, expiresAt := 30, verified := true }

def terms : PurchaseTerms :=
  { merchantId := "ride-provider", productId := "airport-ride",
    offerId := "quote-42", checkoutCommitment := "checkout-42",
    amountMinor := 30000, asset := "HKD" }

def offer : MerchantOffer :=
  { terms, expiresAt := 20, verified := true }

def purchase : Purchase :=
  { purchaseId := "buy-1", mandateId := mandate.mandateId,
    agentId := mandate.agentId, terms }

def budget : Budget :=
  { mandate, now := 10, spentMinor := 0, reservations := [],
    revoked := false, revision := 0 }

def reserved : Budget :=
  { budget with spentMinor := 30000, reservations := [purchase], revision := 1 }

theorem matchingOfferReserves :
    budget.reserve mandate offer purchase = some reserved := by decide
theorem samePurchaseCannotReplay :
    reserved.reserve mandate offer purchase = none := by decide
theorem sameOfferCannotUseNewPurchaseId :
    reserved.reserve mandate offer { purchase with purchaseId := "buy-2" } = none := by decide
theorem wrongAgentDenied :
    budget.reserve mandate offer { purchase with agentId := "other-agent" } = none := by decide
theorem wrongMandateDenied :
    budget.reserve mandate offer { purchase with mandateId := "other-mandate" } = none := by decide
theorem unverifiedMandateDenied :
    budget.reserve { mandate with verified := false } offer purchase = none := by decide
theorem changedPrincipalMandateDenied :
    budget.reserve { mandate with principal := reserveAccount } offer purchase = none := by decide
theorem changedAgentKeyMandateDenied :
    budget.reserve { mandate with agentPublicKey := "other-key" } offer purchase = none := by decide
theorem widenedMerchantMandateDenied :
    budget.reserve { mandate with allowedMerchants := ["ride-provider", "other"] }
      offer purchase = none := by decide
theorem unverifiedOfferDenied :
    budget.reserve mandate { offer with verified := false } purchase = none := by decide
theorem changedMerchantDenied :
    budget.reserve mandate offer
      { purchase with terms := { terms with merchantId := "attacker" } } = none := by decide
theorem changedPriceDenied :
    budget.reserve mandate offer
      { purchase with terms := { terms with amountMinor := 31000 } } = none := by decide
theorem changedProductDenied :
    budget.reserve mandate offer
      { purchase with terms := { terms with productId := "hotel" } } = none := by decide
theorem changedQuoteDenied :
    budget.reserve mandate offer
      { purchase with terms := { terms with offerId := "quote-43" } } = none := by decide
theorem changedCheckoutCommitmentDenied :
    budget.reserve mandate offer
      { purchase with terms := { terms with checkoutCommitment := "checkout-43" } } =
      none := by decide
theorem changedAssetDenied :
    budget.reserve mandate offer
      { purchase with terms := { terms with asset := "USD" } } = none := by decide
theorem outOfScopeMerchantDenied :
    budget.reserve mandate { offer with terms := { terms with merchantId := "other" } }
      { purchase with terms := { terms with merchantId := "other" } } = none := by decide
theorem outOfScopeProductDenied :
    budget.reserve mandate { offer with terms := { terms with productId := "hotel" } }
      { purchase with terms := { terms with productId := "hotel" } } = none := by decide
theorem perPurchaseCapEnforced :
    budget.reserve mandate { offer with terms := { terms with amountMinor := 50001 } }
      { purchase with terms := { terms with amountMinor := 50001 } } = none := by decide
theorem cumulativeCapEnforced :
    ({ budget with spentMinor := 60000 }).reserve mandate offer purchase = none := by decide
def secondTerms : PurchaseTerms :=
  { terms with offerId := "quote-43", amountMinor := 50000 }
def secondOffer : MerchantOffer :=
  { offer with terms := secondTerms }
def secondPurchase : Purchase :=
  { purchase with purchaseId := "buy-2", terms := secondTerms }
theorem twoPurchasesCanUseExactTotalCap :
    (reserved.reserve mandate secondOffer secondPurchase).isSome = true := by decide
theorem zeroPriceDenied :
    budget.reserve mandate { offer with terms := { terms with amountMinor := 0 } }
      { purchase with terms := { terms with amountMinor := 0 } } = none := by decide
theorem revokedMandateDenied :
    ({ budget with revoked := true }).reserve mandate offer purchase = none := by decide
theorem stalePolicyEpochDenied :
    ({ budget with mandate := { mandate with policyEpoch := 5 } }).reserve
      mandate offer purchase = none := by decide
theorem expiredOfferDenied :
    ({ budget with now := 20 }).reserve mandate offer purchase = none := by decide
theorem expiredMandateDenied :
    ({ budget with now := 30 }).reserve mandate
      { offer with expiresAt := 40 } purchase = none := by decide

def child : Mandate :=
  { mandate with mandateId := "trip-child", agentId := "booking-agent-8", agentPublicKey := "agent-key-8", perPurchaseCap := 40000, totalCap := 60000, expiresAt := 25 }
def grant : Delegation :=
  { issuerAgentId := mandate.agentId, parent := mandate,
    child, verified := true }
def grandchild : Mandate :=
  { child with mandateId := "trip-grandchild", agentId := "quote-agent-9", agentPublicKey := "agent-key-9", perPurchaseCap := 35000, totalCap := 50000, expiresAt := 22 }
def secondGrant : Delegation :=
  { issuerAgentId := child.agentId, parent := child,
    child := grandchild, verified := true }

theorem narrowerChildAccepted :
    Delegation.resolveChain mandate [grant] = some child := by decide
theorem twoHopAttenuationAccepted :
    Delegation.resolveChain mandate [grant, secondGrant] =
      some grandchild := by decide
theorem reusedAncestorMandateIdDenied :
    Delegation.resolveChain mandate
      [grant, { secondGrant with child :=
        { grandchild with mandateId := mandate.mandateId } }] = none := by decide
theorem reusedAncestorAgentIdDenied :
    Delegation.resolveChain mandate
      [grant, { secondGrant with child :=
        { grandchild with agentId := mandate.agentId } }] = none := by decide
theorem reusedAncestorAgentKeyDenied :
    Delegation.resolveChain mandate
      [grant, { secondGrant with child :=
        { grandchild with agentPublicKey := mandate.agentPublicKey } }] = none := by decide
theorem widenedMerchantDenied :
    Delegation.resolveChain mandate
      [{ grant with child := { child with allowedMerchants := ["ride-provider", "other"] } }] =
      none := by decide
theorem increasedChildBudgetDenied :
    Delegation.resolveChain mandate
      [{ grant with child := { child with totalCap := 80001 } }] = none := by decide
theorem changedChildPrincipalDenied :
    Delegation.resolveChain mandate
      [{ grant with child := { child with principal := reserveAccount } }] = none := by decide
theorem wrongIssuerDenied :
    Delegation.resolveChain mandate
      [{ grant with issuerAgentId := "other-agent" }] = none := by decide
theorem reusedParentAgentKeyDenied :
    Delegation.resolveChain mandate
      [{ grant with child := { child with agentPublicKey := mandate.agentPublicKey } }] =
      none := by decide
theorem parentSubstitutionDenied :
    Delegation.resolveChain mandate
      [{ grant with parent := { mandate with perPurchaseCap := 60000 } }] = none := by decide
theorem missingHopDenied :
    Delegation.resolveChain mandate [secondGrant] = none := by decide
theorem unverifiedGrantDenied :
    Delegation.resolveChain mandate
      [{ grant with verified := false }] = none := by decide

def credentialBudget : SharedBudget :=
  { root := mandate, now := 10, reservations := [{ lineage := [mandate], purchase }],
    revokedMandateIds := [], revision := 2 }
def commitReceipt : ReservationCommitReceipt :=
  { scope := "buyer-trip-root", operationId := purchase.purchaseId,
    expectedRevision := 1, expectedContentId := "before-cid",
    committedRevision := 2, committedContentId := "after-cid",
    reservation := { lineage := [mandate], purchase }, verified := true }
def credential : Credential :=
  { credentialId := "agent-token-1", issuerId := "credential-provider",
    receipt := commitReceipt, expiresAt := 18, verified := true }

theorem exactCredentialAccepted :
    credentialBudget.acceptsCredential "buyer-trip-root" offer purchase credential = true := by decide
theorem credentialCannotPrecedeReservation :
    ({ credentialBudget with reservations := [] }).acceptsCredential "buyer-trip-root"
      offer purchase credential = false := by decide
theorem otherAgentCredentialDenied :
    credentialBudget.acceptsCredential "buyer-trip-root" offer purchase
      { credential with receipt := { commitReceipt with
        reservation := { lineage := [child], purchase } } } = false := by decide
theorem otherCheckoutCredentialDenied :
    credentialBudget.acceptsCredential "buyer-trip-root"
      { offer with terms := { terms with checkoutCommitment := "other-checkout" } }
      purchase credential = false := by decide
theorem expiredCredentialDenied :
    ({ credentialBudget with now := 18 }).acceptsCredential "buyer-trip-root"
      offer purchase credential = false := by decide
theorem revokedCredentialDenied :
    (credentialBudget.revoke mandate.mandateId).acceptsCredential "buyer-trip-root"
      offer purchase credential = false := by decide
theorem unverifiedCredentialDenied :
    credentialBudget.acceptsCredential "buyer-trip-root" offer purchase
      { credential with verified := false } = false := by decide

def cardProfile : AgenticCommercePaymentProfile :=
  { budgetScope := "buyer-trip-root", origin := admin, instrument := "agent-card-token", network := "card",
    feeCap := "1.0000", verified := true }
def payment : PaymentOperation :=
  { authorityMode := .delegated, payerAccount := approvedAccount, origin := admin,
    instrument := "agent-card-token", beneficiary := terms.merchantId,
    amount := "300.0000", asset := "HKD", network := "card",
    feeCap := "1.0000", mandateRef := mandate.mandateId,
    checkoutCommitment := terms.checkoutCommitment,
    nonce := purchase.purchaseId, proposer := mandate.agentId,
    policyEpoch := mandate.policyEpoch, expiresAt := 18 }
def envelope : AgenticCommercePaymentEnvelope :=
  { offer, purchase, credential, payment }

theorem exactPurchaseBindsPayment :
    cardProfile.binds credentialBudget envelope = true := by native_decide
theorem changedPaymentMerchantDenied :
    cardProfile.binds credentialBudget
      { envelope with payment := { payment with beneficiary := "other" } } = false := by native_decide
theorem changedPaymentAmountDenied :
    cardProfile.binds credentialBudget
      { envelope with payment := { payment with amount := "301.0000" } } = false := by native_decide
theorem nonCanonicalPaymentAmountDenied :
    cardProfile.binds credentialBudget
      { envelope with payment := { payment with amount := "300.00" } } = false := by native_decide
theorem changedCheckoutInPaymentDenied :
    cardProfile.binds credentialBudget
      { envelope with payment := { payment with checkoutCommitment := "other" } } = false := by native_decide
theorem changedPaymentNonceDenied :
    cardProfile.binds credentialBudget
      { envelope with payment := { payment with nonce := "buy-2" } } = false := by native_decide
theorem wrongPaymentAgentDenied :
    cardProfile.binds credentialBudget
      { envelope with payment := { payment with proposer := "other-agent" } } = false := by native_decide
theorem expiredPaymentDenied :
    cardProfile.binds credentialBudget
      { envelope with payment := { payment with expiresAt := 21 } } = false := by native_decide

def sharedBudget : SharedBudget :=
  { root := mandate, now := 10, reservations := [], revokedMandateIds := [], revision := 0 }

def childPurchase : Purchase :=
  { purchase with mandateId := child.mandateId, agentId := child.agentId }

def sharedAfterChild : SharedBudget :=
  { sharedBudget with
    reservations := [{ lineage := [mandate, child], purchase := childPurchase }]
    revision := 1 }

def sibling : Mandate :=
  { child with
    mandateId := "trip-sibling", agentId := "booking-agent-10"
    agentPublicKey := "agent-key-10" }

def siblingGrant : Delegation :=
  { grant with child := sibling }

def siblingTerms : PurchaseTerms :=
  { terms with offerId := "sibling-quote", checkoutCommitment := "sibling-checkout" }

def siblingPurchase : Purchase :=
  { purchase with
    purchaseId := "sibling-buy", mandateId := sibling.mandateId
    agentId := sibling.agentId, terms := siblingTerms }

def sharedAfterSiblings : SharedBudget :=
  { sharedAfterChild with
    reservations := { lineage := [mandate, sibling], purchase := siblingPurchase } ::
      sharedAfterChild.reservations
    revision := 2 }

theorem sharedChildReserves :
    sharedBudget.reserve 0 [grant] offer childPurchase = some sharedAfterChild := by decide

theorem siblingsChargeOneRoot :
    sharedAfterChild.reserve 1 [siblingGrant] { offer with terms := siblingTerms }
      siblingPurchase = some sharedAfterSiblings := by decide

theorem siblingsShareRootTotal : sharedAfterSiblings.spentMinor = 60000 := by decide
theorem childrenKeepSeparateCaps : sharedAfterSiblings.spentUnder child.mandateId = 30000 := by decide

theorem competingSiblingCannotUsePreparedRevision :
    sharedAfterChild.reserve 0 [siblingGrant] { offer with terms := siblingTerms }
      siblingPurchase = none := by decide

theorem siblingsCannotExceedRootCap :
    sharedAfterSiblings.reserve 2 [grant]
      { offer with terms := { terms with offerId := "third-quote" } }
      { childPurchase with
        purchaseId := "third-buy"
        terms := { terms with offerId := "third-quote" } } = none := by decide

theorem duplicateOfferCannotMoveToSibling :
    sharedAfterChild.reserve 1 [siblingGrant] offer
      { siblingPurchase with terms := terms } = none := by decide

theorem rootRevocationDeniesFreshChild :
    (sharedBudget.revoke mandate.mandateId).reserve 1 [grant] offer childPurchase = none := by decide

theorem parentRevocationDeniesFreshGrandchild :
    (sharedBudget.revoke child.mandateId).reserve 1 [grant, secondGrant] offer
      { purchase with mandateId := grandchild.mandateId, agentId := grandchild.agentId } =
      none := by decide

theorem branchRevocationDoesNotRevokeSibling :
    ((sharedBudget.revoke child.mandateId).reserve 1 [siblingGrant]
      { offer with terms := siblingTerms } siblingPurchase).isSome = true := by decide

theorem reusedChildIdCannotResetBudgetContents :
    sharedAfterChild.reserve 1 [{ grant with child := { child with totalCap := 70000 } }]
      { offer with terms := { terms with offerId := "renewed-quote" } }
      { childPurchase with
        purchaseId := "renewed-buy"
        terms := { terms with offerId := "renewed-quote" } } = none := by decide

def cousin : Mandate :=
  { grandchild with
    mandateId := "trip-cousin", agentId := "quote-agent-11"
    agentPublicKey := "agent-key-11" }

def cousinGrant : Delegation :=
  { secondGrant with child := cousin }

def grandchildTerms : PurchaseTerms :=
  { terms with amountMinor := 35000 }

def grandchildPurchase : Purchase :=
  { purchase with
    mandateId := grandchild.mandateId, agentId := grandchild.agentId
    terms := grandchildTerms }

def sharedAfterGrandchild : SharedBudget :=
  { sharedBudget with
    reservations := [{ lineage := [mandate, child, grandchild], purchase := grandchildPurchase }]
    revision := 1 }

theorem grandchildChargesAllAncestors :
    sharedBudget.reserve 0 [grant, secondGrant] { offer with terms := grandchildTerms }
      grandchildPurchase = some sharedAfterGrandchild := by decide

theorem cousinsCannotExceedTheirParentCap :
    sharedAfterGrandchild.reserve 1 [grant, cousinGrant]
      { offer with terms := siblingTerms }
      { siblingPurchase with mandateId := cousin.mandateId, agentId := cousin.agentId } =
      none := by decide

theorem grandchildCannotExceedOwnCumulativeCap :
    sharedAfterGrandchild.reserve 1 [grant, secondGrant]
      { offer with terms := { siblingTerms with amountMinor := 20000 } }
      { siblingPurchase with
        mandateId := grandchild.mandateId, agentId := grandchild.agentId
        terms := { siblingTerms with amountMinor := 20000 } } = none := by decide

theorem laterRevisionRetainsCredential :
    ({ credentialBudget with revision := 5 }).acceptsCredential "buyer-trip-root"
      offer purchase credential = true := by decide
theorem futureCommitReceiptDenied :
    credentialBudget.acceptsCredential "buyer-trip-root" offer purchase
      { credential with receipt := { commitReceipt with expectedRevision := 2, committedRevision := 3 } } = false := by decide
theorem unverifiedCommitReceiptDenied :
    credentialBudget.acceptsCredential "buyer-trip-root" offer purchase
      { credential with receipt := { commitReceipt with verified := false } } = false := by decide
theorem wrongReceiptScopeDenied :
    credentialBudget.acceptsCredential "other-scope" offer purchase credential = false := by decide
theorem wrongReceiptOperationDenied :
    credentialBudget.acceptsCredential "buyer-trip-root" offer purchase
      { credential with receipt := { commitReceipt with operationId := "other" } } = false := by decide
theorem identicalCommitContentDenied :
    credentialBudget.acceptsCredential "buyer-trip-root" offer purchase
      { credential with receipt := { commitReceipt with committedContentId := "before-cid" } } =
      false := by decide
theorem credentialCannotOutliveOffer :
    credentialBudget.acceptsCredential "buyer-trip-root" offer purchase
      { credential with expiresAt := 21 } = false := by decide

def childCredential : Credential :=
  { credential with
    receipt := { commitReceipt with
      expectedRevision := 1
      committedRevision := 2
      operationId := childPurchase.purchaseId
      reservation := { lineage := [mandate, child], purchase := childPurchase } } }
theorem committedChildCredentialAccepted :
    ({ sharedAfterChild with revision := 2 }).acceptsCredential "buyer-trip-root"
      offer childPurchase childCredential =
      true := by decide
theorem revokedAncestorDeniesChildCredential :
    (sharedAfterChild.revoke mandate.mandateId).acceptsCredential "buyer-trip-root"
      offer childPurchase childCredential = false := by decide
theorem changedRootDeniesCredential :
    ({ sharedAfterChild with root := { mandate with policyEpoch := 5 } }).acceptsCredential
      "buyer-trip-root" offer childPurchase childCredential = false := by decide

theorem delegatedCredentialBindsLeafPayment :
    cardProfile.binds { sharedAfterChild with revision := 2 }
      { envelope with
        purchase := childPurchase
        credential := childCredential
        payment := { payment with mandateRef := child.mandateId, proposer := child.agentId } } =
      true := by native_decide
theorem parentCannotReplaceLeafPaymentAuthority :
    cardProfile.binds { sharedAfterChild with revision := 2 }
      { envelope with purchase := childPurchase, credential := childCredential } =
      false := by native_decide
theorem revokedAncestorDeniesPaymentBinding :
    cardProfile.binds (credentialBudget.revoke mandate.mandateId) envelope = false := by native_decide
theorem wrongPaymentBudgetScopeDenied :
    ({ cardProfile with budgetScope := "other-root" }).binds credentialBudget envelope =
      false := by native_decide


/-- General laws are consumed with the same root/child/grandchild Cases as
the existing semantic and native signature-admission controls. -/
theorem completeLineageHasUniqueIdentities :
    (mandate.mandateId :: [grant, secondGrant].map (·.child.mandateId)).Nodup ∧
    (mandate.agentId :: [grant, secondGrant].map (·.child.agentId)).Nodup ∧
    (mandate.agentPublicKey :: [grant, secondGrant].map (·.child.agentPublicKey)).Nodup :=
  Delegation.resolvedLineageUnique twoHopAttenuationAccepted

theorem siblingReservationsRetainExactRootAndDebits :
    sharedBudget.retains sharedAfterSiblings :=
  SharedBudget.retains_trans
    (sharedReservationRetainsHistory sharedChildReserves)
    (sharedReservationRetainsHistory siblingsChargeOneRoot)

theorem siblingReservationCannotRefundChild :
    sharedAfterChild.spentUnder child.mandateId ≤
      sharedAfterSiblings.spentUnder child.mandateId :=
  SharedBudget.retained_ancestor_spend
    (sharedReservationRetainsHistory siblingsChargeOneRoot) _

theorem revokedAncestorAfterEveryFiniteHistory
    (framework : CedarPooSpec.ZeroTrust.Framework Unit SharedBudget)
    (run : CedarPooSpec.ZeroTrust.Run framework (SharedBudget.Step Unit)
      (sharedAfterChild.revoke child.mandateId) current) :
    current.reserve current.revision [grant, secondGrant]
      { offer with terms := grandchildTerms } grandchildPurchase = none :=
  SharedBudget.revoked_ancestor_blocks_run (mandate := child) framework run
    (by simp [SharedBudget.revoke]) (by simp [grant])

def contractedSharedProposal : Option SharedBudget := do
  let .ok receipt := SharedBudget.reservationContract.invoke SharedBudget.prepareReservation {
    state := sharedBudget, expectedRevision := 0,
    steps := [grant], offer, purchase := childPurchase } | none
  pure receipt.result

theorem contractUsesActualSharedAllocator :
    contractedSharedProposal = some sharedAfterChild := by decide


def revokedContractProposal : Option SharedBudget := do
  let .ok receipt := SharedBudget.reservationContract.invoke SharedBudget.prepareReservation {
    state := sharedBudget.revoke child.mandateId, expectedRevision := 1,
    steps := [grant], offer, purchase := childPurchase } | none
  pure receipt.result

theorem contractRefusesRevokedChild : revokedContractProposal = none := by decide

/-- A syntactically fresh ledger is not a recovery successor of a spent head. -/
theorem oldCheckpointCannotRefundSibling :
    ¬ sharedAfterSiblings.retains sharedAfterChild := by
  intro retained
  have spend := SharedBudget.retained_spend retained
  simp [SharedBudget.spentMinor, sharedAfterSiblings, sharedAfterChild,
    sharedBudget, siblingPurchase, siblingTerms, childPurchase, purchase, terms] at spend

#print axioms Delegation.resolvedLineageUnique
#print axioms SharedBudget.run_retains
#print axioms SharedBudget.retained_ancestor_spend
#print axioms SharedBudget.run_preserves_root_cap
#print axioms SharedBudget.revoked_ancestor_blocks_run
#print axioms SharedBudget.reservation_receipt_retains
#print axioms SharedBudget.reservation_receipt_lineage_unique
#print axioms SharedBudget.reservation_receipt_root_cap

end CedarPooSpec.AgenticAI.CommerceTest
