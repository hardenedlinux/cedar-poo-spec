import CedarPooSpec.AgenticAI.Commerce.Credential
import CedarPooSpec.Gateway.OAuthRevocationCrash
import CedarPooSpec.Vertical.FinancialServices.PaymentOperation

/-!
A public payment-operation adapter for an admitted agent purchase. This
profile uses HKD cents to show exact amount conversion. The Host still
authenticates the credential, checkout, and policy inputs, and must carry the
complete envelope to the provider. No card token is issued here.
-/

namespace CedarPooSpec.Vertical.FinancialServices

open CedarPooSpec.AgenticAI.Commerce

/-- This profile uses HKD cents while Cedar decimals use four fractional
    places. A canonical amount must therefore be an integer number of cents. -/
def canonicalHkdCents (text : String) : Option Nat := do
  let value ← Cedar.Spec.Ext.Decimal.decimal text
  if toString value != text then none else
  if value.toInt > 0 && value.toInt % 100 == 0 then
    some (value.toInt.toNat / 100)
  else none

structure AgenticCommercePaymentProfile where
  budgetScope : String
  origin : Cedar.Spec.EntityUID
  instrument : String
  network : String
  feeCap : String
  verified : Bool
  deriving DecidableEq, Repr

/-- The full envelope is needed at the Host's credential and payment boundary;
    `checkoutCommitment` on `PaymentOperation` carries the offer binding into
    downstream payment evidence. -/
structure AgenticCommercePaymentEnvelope where
  offer : MerchantOffer
  purchase : Purchase
  credential : Credential
  payment : PaymentOperation
  deriving DecidableEq, Repr

/-- Check correspondence only. Cedar authorization and Host effect release are
    separate decisions after this predicate succeeds. -/
def AgenticCommercePaymentProfile.binds (profile : AgenticCommercePaymentProfile)
    (budget : SharedBudget)
    (envelope : AgenticCommercePaymentEnvelope) : Bool :=
  profile.verified && !profile.instrument.isEmpty &&
  !profile.network.isEmpty &&
  budget.acceptsCredential profile.budgetScope envelope.offer envelope.purchase envelope.credential &&
  envelope.payment.wellFormed &&
  envelope.payment.authorityMode == .delegated &&
  decide (envelope.payment.payerAccount = budget.root.principal) &&
  decide (envelope.payment.origin = profile.origin) &&
  envelope.payment.instrument == profile.instrument &&
  envelope.payment.network == profile.network &&
  envelope.payment.feeCap == profile.feeCap &&
  envelope.payment.beneficiary == envelope.purchase.terms.merchantId &&
  envelope.payment.asset == envelope.purchase.terms.asset &&
  envelope.payment.checkoutCommitment ==
    envelope.purchase.terms.checkoutCommitment &&
  envelope.payment.mandateRef == envelope.purchase.mandateId &&
  envelope.payment.nonce == envelope.purchase.purchaseId &&
  envelope.payment.proposer == envelope.purchase.agentId &&
  envelope.payment.policyEpoch == budget.root.policyEpoch &&
  budget.now < envelope.payment.expiresAt &&
  envelope.payment.expiresAt <= budget.root.expiresAt &&
  envelope.payment.expiresAt <= envelope.offer.expiresAt &&
  envelope.payment.expiresAt <= envelope.credential.expiresAt &&
  canonicalHkdCents envelope.payment.amount ==
    some envelope.purchase.terms.amountMinor


open CedarPooSpec.Gateway.OAuth.Revocation.Crash
open LeanPoo.Functional.DeclarativeMetadata

/-- Both projections of the authoritative write. An observer receives neither
component when one of the two exact reservations is refused. -/
structure DelegatedCommitInput where
  effect : CurrentCommitInput
  budget : SharedBudget.ReservationInput
  independentBudget : SharedBudget
  authorizedLineage : List Mandate
  authorizedPurchase : Purchase

/-- Exact typed projection of the commerce commitment checked by Cedar.
Native code binds this projection by digest and reauthenticates the signed inputs. -/
def DelegatedCommitInput.current (input : DelegatedCommitInput) : Prop :=
  input.independentBudget = input.budget.state ∧
  input.effect.request.operation = input.budget.purchase.purchaseId ∧
  input.authorizedLineage = input.budget.state.root :: input.budget.steps.map (·.child) ∧
  input.authorizedPurchase = input.budget.purchase ∧
  input.budget.state.root.policyEpoch = input.effect.envelope.review.epoch ∧
  input.budget.state.now = input.effect.actual.authority.now

instance (input : DelegatedCommitInput) : Decidable input.current := by
  unfold DelegatedCommitInput.current
  infer_instance

def DelegatedCommitInput.commit (input : DelegatedCommitInput) :
    Option (Image × SharedBudget) := do
  if input.current then
    let effect ← input.effect.reserve
    let budget ← input.budget.state.reserve input.budget.expectedRevision
      input.budget.steps input.budget.offer input.budget.purchase
    some (effect, budget)
  else none

def delegatedCommitContract : Contract Unit DelegatedCommitInput (Image × SharedBudget) where
  input := ⟨"same-operation-current-effect-and-shared-budget", DelegatedCommitInput.current,
    fun _ => inferInstance⟩
  output := ⟨"joint-charge-and-effect-reservation", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => input.commit = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareDelegatedCommit (input : DelegatedCommitInput) :
    Except String ((Image × SharedBudget) × Unit) :=
  match input.commit with
  | some result => .ok (result, ())
  | none => .error "Delegated effect reservation refused"

theorem delegated_commit_exact
    (receipt : Invocation delegatedCommitContract prepareDelegatedCommit input) :
    input.effect.reserve = some receipt.result.1 ∧
    input.budget.state.reserve input.budget.expectedRevision input.budget.steps
      input.budget.offer input.budget.purchase = some receipt.result.2 := by
  have accepted := receipt.logic
  change input.commit = some receipt.result at accepted
  have current : input.current := receipt.input
  unfold DelegatedCommitInput.commit at accepted
  rw [if_pos current] at accepted
  cases effect : input.effect.reserve with
  | none => simp [effect] at accepted
  | some reserved =>
    cases budget : input.budget.state.reserve input.budget.expectedRevision input.budget.steps
        input.budget.offer input.budget.purchase with
    | none => simp [effect, budget] at accepted
    | some charged =>
      simp [effect, budget] at accepted
      rw [← accepted]
      exact ⟨rfl, rfl⟩

theorem delegated_commit_preserves_debits
    (receipt : Invocation delegatedCommitContract prepareDelegatedCommit input) :
    input.budget.state.retains receipt.result.2 ∧
    receipt.result.2.spentMinor ≤ input.budget.state.root.totalCap := by
  have applied := (delegated_commit_exact receipt).2
  exact ⟨sharedReservationRetainsHistory applied,
    sharedReservationPreservesRootCap _ _ _ _ _ _ applied⟩

theorem delegated_commit_refuses_stale_budget (input : DelegatedCommitInput)
    (stale : input.independentBudget ≠ input.budget.state) : input.commit = none := by
  simp [DelegatedCommitInput.commit, DelegatedCommitInput.current, stale]

end CedarPooSpec.Vertical.FinancialServices
