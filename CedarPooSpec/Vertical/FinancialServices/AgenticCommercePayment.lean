import CedarPooSpec.AgenticAI.Commerce.Credential
import CedarPooSpec.Gateway.OAuthReceiver
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

/-- A later admitted delegated payment keeps every previously burned OAuth
    operation in the image on which its final admission actually ran. -/
theorem delegated_commit_preserves_prior_hold
    (receipt : Invocation delegatedCommitContract prepareDelegatedCommit input)
    (burned : (input.effect.request.image.retained.any fun row =>
      row.intent.operation == operation) = true) :
    (receipt.result.1.retained.any fun row => row.intent.operation == operation) = true := by
  have applied := (delegated_commit_exact receipt).1
  unfold CurrentCommitInput.reserve at applied
  split at applied
  · let prior : Invocation beginContract prepareBegin input.effect.request :=
      ⟨receipt.result.1, (), by simp [prepareBegin, applied], trivial, trivial, applied⟩
    exact begin_preserves_prior_burn prior burned
  · contradiction

theorem delegated_commit_refuses_stale_budget (input : DelegatedCommitInput)
    (stale : input.independentBudget ≠ input.budget.state) : input.commit = none := by
  simp [DelegatedCommitInput.commit, DelegatedCommitInput.current, stale]

/-- A worker prepared against the same budget revision cannot commit after
    another worker wins, even if it reloads the winning budget. The Host must
    serialize the actual comparison and write; this theorem models that order. -/
theorem delegated_commit_refuses_losing_revision
    (winner loser : DelegatedCommitInput)
    (receipt : Invocation delegatedCommitContract prepareDelegatedCommit winner)
    (sameRevision : loser.budget.expectedRevision = winner.budget.state.revision) :
    (let budget := { loser.budget with state := receipt.result.2 }
     let rebound := { loser with budget := budget, independentBudget := receipt.result.2 }
     rebound.commit = none) := by
  have advanced := sharedReservationAdvancesRevision _ _ _ _ _ _
    (delegated_commit_exact receipt).2
  have stale : loser.budget.expectedRevision ≠ receipt.result.2.revision := by
    rw [sameRevision, advanced]
    omega
  simp [DelegatedCommitInput.commit, sharedStaleRevisionCannotReserve, stale]

/-- Refreshing the OAuth view does not make a losing budget revision current.
    The effect parameter may contain the winner's exact committed image and a
    new proof; the revision check remains independent of effect admission. -/
theorem delegated_commit_refuses_losing_revision_with_current_oauth
    (winner loser : DelegatedCommitInput) (currentEffect : CurrentCommitInput)
    (receipt : Invocation delegatedCommitContract prepareDelegatedCommit winner)
    (sameRevision : loser.budget.expectedRevision = winner.budget.state.revision) :
    (let budget := { loser.budget with state := receipt.result.2 }
     let rebound := { loser with effect := currentEffect, budget := budget, independentBudget := receipt.result.2 }
     rebound.commit = none) := by
  have advanced := sharedReservationAdvancesRevision _ _ _ _ _ _
    (delegated_commit_exact receipt).2
  have stale : loser.budget.expectedRevision ≠ receipt.result.2.revision := by
    rw [sameRevision, advanced]
    omega
  simp [DelegatedCommitInput.commit, sharedStaleRevisionCannotReserve, stale]

open CedarPooSpec.Gateway.OAuth

/-- Recovery uses the same OAuth operation inventory and shared budget as
final submission. Receiver evidence is read from its independent checkpoint. -/
inductive DelegatedRecoveryCommand where
  | handoff (writer : Nat)
  | revoke (writer : Nat) (grant : PAR.VerifiedClient Refresh.RefreshDigest) (mandate : String)
  | reconcile (input : Receiver.ManagedReconciliation)

structure DelegatedRecoveryInput where
  state : Image × SharedBudget
  command : DelegatedRecoveryCommand

def DelegatedRecoveryInput.apply (input : DelegatedRecoveryInput) : Option (Image × SharedBudget) := do
  let (image, budget) := input.state
  match input.command with
  | .handoff writer => return (← handoff image writer, budget)
  | .revoke writer grant mandate => return (← revoke image writer grant, budget.revoke mandate)
  | .reconcile observation =>
    if observation.audit.image = image then
      return (← Receiver.reconcileManaged observation, budget)
    else none

def delegatedRecoveryContract : Contract Unit DelegatedRecoveryInput (Image × SharedBudget) where
  input := ⟨"retained-payment-state-and-recovery-command", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"recovery-preserves-payment-hold", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => input.apply = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareDelegatedRecovery (input : DelegatedRecoveryInput) :
    Except String ((Image × SharedBudget) × Unit) :=
  match input.apply with
  | some state => .ok (state, ())
  | none => .error "Delegated payment recovery refused"

theorem delegated_recovery_preserves_reservations
    (receipt : Invocation delegatedRecoveryContract prepareDelegatedRecovery input) :
    receipt.result.1.retained = input.state.1.retained ∧
    receipt.result.2.reservations = input.state.2.reservations := by
  have accepted : input.apply = some receipt.result := receipt.logic
  obtain ⟨⟨image, budget⟩, command⟩ := input
  cases command with
  | handoff writer =>
    cases step : handoff image writer with
    | none => simp [DelegatedRecoveryInput.apply, step] at accepted
    | some after =>
      simp [DelegatedRecoveryInput.apply, step] at accepted
      rw [← accepted]
      exact ⟨(handoff_preserves_effect_state step).1, rfl⟩
  | revoke writer grant mandate =>
    cases step : revoke image writer grant with
    | none => simp [DelegatedRecoveryInput.apply, step] at accepted
    | some after =>
      simp [DelegatedRecoveryInput.apply, step] at accepted
      rw [← accepted]
      exact ⟨(revocation_preserves_effect_state step).1, rfl⟩
  | reconcile observation =>
    by_cases actual : observation.audit.image = image
    · cases step : Receiver.reconcileManaged observation with
      | none => simp [DelegatedRecoveryInput.apply, actual, step] at accepted
      | some after =>
        simp [DelegatedRecoveryInput.apply, actual, step] at accepted
        rw [← accepted]
        obtain ⟨evidence, observed⟩ : ∃ evidence, observation.observation = some evidence := by
          cases observed : observation.observation with
          | none => simp [Receiver.reconcileManaged, observed] at step
          | some evidence => exact ⟨evidence, rfl⟩
        have applied : reconcileFrom observation.audit (some evidence) = some after := by
          simpa [Receiver.reconcileManaged, observed] using step
        exact ⟨(reconciliation_from_preserves_authority applied).2.2.trans (congrArg Image.retained actual), rfl⟩
    · simp [DelegatedRecoveryInput.apply, actual] at accepted

theorem delegated_recovery_cannot_reopen_operation
    (receipt : Invocation delegatedRecoveryContract prepareDelegatedRecovery input)
    (same : retry.image = receipt.result.1)
    (burned : (input.state.1.retained.any fun row => row.intent.operation == retry.operation) = true) :
    begin retry = none := by
  apply burned_operation_cannot_begin
  simpa only [same, (delegated_recovery_preserves_reservations receipt).1] using burned


end CedarPooSpec.Vertical.FinancialServices
