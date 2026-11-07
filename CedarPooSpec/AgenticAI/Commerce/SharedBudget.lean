import CedarPooSpec.AgenticAI.Commerce.Delegation
import CedarPooSpec.ZeroTrust.Continuous
import LeanPoo.Functional.DeclarativeMetadata

/-!
One shared allocator for a principal mandate and all its delegated branches.
Every reservation charges the root and each ancestor on its exact lineage.
The Host reauthenticates current evidence and persists this transition with an
atomic revision comparison; this pure model is not a storage transaction.
-/

namespace CedarPooSpec.AgenticAI.Commerce

/-- Keep complete authority contents, so reusing an ID cannot reset its cap. -/
structure SharedReservation where
  lineage : List Mandate
  purchase : Purchase
  deriving DecidableEq, Repr

structure SharedBudget where
  root : Mandate
  now : Nat
  reservations : List SharedReservation
  revokedMandateIds : List String
  revision : Nat
  deriving DecidableEq, Repr

def SharedBudget.spentMinor (state : SharedBudget) : Nat :=
  (state.reservations.map (fun entry => entry.purchase.terms.amountMinor)).sum

/-- A grandchild's purchase also consumes the shared cap of its parent. -/
def SharedBudget.spentUnder (state : SharedBudget)
    (mandateId : String) : Nat :=
  ((state.reservations.filter (fun entry =>
    entry.lineage.any (fun mandate => mandate.mandateId == mandateId))).map
      (fun entry => entry.purchase.terms.amountMinor)).sum

private def SharedBudget.admitsLineage (state : SharedBudget)
    (lineage : List Mandate) (final : Mandate)
    (offer : MerchantOffer) (purchase : Purchase) : Bool :=
  lineage.all (fun mandate =>
    mandate.verified && state.now < mandate.expiresAt &&
    !state.revokedMandateIds.contains mandate.mandateId &&
    state.spentUnder mandate.mandateId + offer.terms.amountMinor <= mandate.totalCap &&
    state.reservations.all (fun entry => entry.lineage.all (fun previous =>
      previous.mandateId != mandate.mandateId || decide (previous = mandate)))) &&
  ({ mandate := final, now := state.now,
     spentMinor := state.spentUnder final.mandateId,
     reservations := state.reservations.map (·.purchase),
     revoked := false, revision := state.revision } : Budget).admits
       final offer purchase

/-- The expected revision belongs to the shared root, never to an individual child.
    Scope, ancestor caps, duplicate purchases/offers, and revocation are checked
    against the state that wins the Host's atomic transaction. -/
def SharedBudget.reserve (state : SharedBudget)
    (expectedRevision : Nat) (steps : List Delegation)
    (offer : MerchantOffer) (purchase : Purchase) : Option SharedBudget :=
  if expectedRevision = state.revision then
    if state.spentMinor + purchase.terms.amountMinor <= state.root.totalCap then
      match Delegation.resolveChain state.root steps with
      | none => none
      | some final =>
          let lineage := state.root :: steps.map (·.child)
          if state.admitsLineage lineage final offer purchase then
            some { state with
              reservations := { lineage, purchase } :: state.reservations,
              revision := state.revision + 1 }
          else none
    else none
  else none

/-- Revocation invalidates prepared revisions and every descendant of this ID. -/
def SharedBudget.revoke (state : SharedBudget)
    (mandateId : String) : SharedBudget :=
  { state with
    revokedMandateIds := mandateId :: state.revokedMandateIds
    revision := state.revision + 1 }

theorem sharedStaleRevisionCannotReserve (state : SharedBudget)
    (expectedRevision : Nat) (steps : List Delegation)
    (offer : MerchantOffer) (purchase : Purchase)
    (h : expectedRevision ≠ state.revision) :
    state.reserve expectedRevision steps offer purchase = none := by
  simp [SharedBudget.reserve, h]

theorem sharedReservationAdvancesRevision (state next : SharedBudget)
    (expectedRevision : Nat) (steps : List Delegation)
    (offer : MerchantOffer) (purchase : Purchase)
    (h : state.reserve expectedRevision steps offer purchase = some next) :
    next.revision = state.revision + 1 := by
  unfold SharedBudget.reserve at h
  split at h <;> simp_all
  split at h <;> simp_all
  rcases h with ⟨_, _, rfl⟩
  rfl

theorem sharedReservationPreservesRootCap (state next : SharedBudget)
    (expectedRevision : Nat) (steps : List Delegation)
    (offer : MerchantOffer) (purchase : Purchase)
    (h : state.reserve expectedRevision steps offer purchase = some next) :
    next.spentMinor <= state.root.totalCap := by
  unfold SharedBudget.reserve at h
  split at h <;> simp_all
  split at h <;> simp_all
  rcases h with ⟨hcap, _, rfl⟩
  simpa [SharedBudget.spentMinor, Nat.add_comm] using hcap

/-- A later independently selected head keeps the exact root, every original
reservation (including multiplicity), committed revocations and monotone clocks.
This is a semantic relation, not authentication of a serialized snapshot. -/
def SharedBudget.retains (before after : SharedBudget) : Prop :=
  after.root = before.root ∧
  (∃ added, after.reservations = added ++ before.reservations) ∧
  (∀ id ∈ before.revokedMandateIds, id ∈ after.revokedMandateIds) ∧
  before.revision ≤ after.revision ∧ before.now ≤ after.now

theorem SharedBudget.retains_refl (state : SharedBudget) : state.retains state :=
  ⟨rfl, ⟨[], rfl⟩, fun _ h => h, Nat.le_refl _, Nat.le_refl _⟩

theorem SharedBudget.retains_trans {a b c : SharedBudget}
    (first : a.retains b) (second : b.retains c) : a.retains c := by
  obtain ⟨front, hfront⟩ := first.2.1
  obtain ⟨back, hback⟩ := second.2.1
  exact ⟨second.1.trans first.1,
    ⟨back ++ front, by simp [hback, hfront, List.append_assoc]⟩,
    fun id h => second.2.2.1 id (first.2.2.1 id h),
    Nat.le_trans first.2.2.2.1 second.2.2.2.1,
    Nat.le_trans first.2.2.2.2 second.2.2.2.2⟩

variable {E : Type} {before after original current : SharedBudget}

theorem sharedReservationRetainsHistory
    (applied : before.reserve revision steps offer purchase = some after) :
    before.retains after := by
  unfold SharedBudget.reserve at applied
  split at applied <;> simp_all
  split at applied <;> simp_all
  rcases applied with ⟨_, _, rfl⟩
  exact ⟨rfl, ⟨[⟨before.root :: steps.map (·.child), purchase⟩], rfl⟩,
    fun _ h => h, Nat.le_succ _, Nat.le_refl _⟩

theorem sharedRevocationRetainsHistory (state : SharedBudget) (id : String) :
    state.retains (state.revoke id) :=
  ⟨rfl, ⟨[], rfl⟩, fun _ h => List.mem_cons_of_mem _ h,
    Nat.le_succ _, Nat.le_refl _⟩

/-- Reserve and revoke are the existing algorithms. An unchanged projection
permits observation/owner changes only when the budget itself is preserved. -/
inductive SharedBudget.Step (E : Type) : SharedBudget → Option E → SharedBudget → Prop where
  | reserved {before after : SharedBudget} {revision : Nat}
      {steps : List Delegation} {offer : MerchantOffer} {purchase : Purchase} {effect : E}
      (applied : before.reserve revision steps offer purchase = some after) :
      Step E before (some effect) after
  | revoked (state : SharedBudget) (id : String) : Step E state none (state.revoke id)
  | unchanged (state : SharedBudget) : Step E state none state

theorem SharedBudget.step_retains (step : Step E before effect after) :
    before.retains after := by
  cases step with
  | reserved applied => exact sharedReservationRetainsHistory applied
  | revoked id => exact sharedRevocationRetainsHistory _ id
  | unchanged => exact retains_refl _

/-- Every finite mediated history preserves the exact debit and revocation
history. No approval, retry, child agent or maintenance label resets the root. -/
theorem SharedBudget.run_retains
    (framework : CedarPooSpec.ZeroTrust.Framework E SharedBudget)
    (run : CedarPooSpec.ZeroTrust.Run framework (Step E) original current) :
    original.retains current :=
  CedarPooSpec.ZeroTrust.run_preserves (SharedBudget.retains original)
    (fun _ _ _ step prior => retains_trans prior (step_retains step))
    (retains_refl original) run

theorem SharedBudget.retained_reservation {reservation : SharedReservation} (retained : before.retains after)
    (known : reservation ∈ before.reservations) : reservation ∈ after.reservations := by
  obtain ⟨added, changed⟩ := retained.2.1
  simp [changed, known]

theorem SharedBudget.retained_spend (retained : before.retains after) :
    before.spentMinor ≤ after.spentMinor := by
  obtain ⟨added, changed⟩ := retained.2.1
  simp [spentMinor, changed, List.sum_append]

theorem SharedBudget.retained_ancestor_spend (retained : before.retains after) (id : String) :
    before.spentUnder id ≤ after.spentUnder id := by
  obtain ⟨added, changed⟩ := retained.2.1
  simp [spentUnder, changed, List.filter_append, List.sum_append]

theorem SharedBudget.run_preserves_root_cap
    (framework : CedarPooSpec.ZeroTrust.Framework E SharedBudget)
    (run : CedarPooSpec.ZeroTrust.Run framework (Step E) original current)
    (safe : original.spentMinor ≤ original.root.totalCap) :
    current.spentMinor ≤ current.root.totalCap := by
  apply CedarPooSpec.ZeroTrust.run_preserves
    (fun state : SharedBudget => state.spentMinor ≤ state.root.totalCap) ?_ safe run
  intro before effect after step prior
  cases step with
  | reserved applied =>
    have root := (sharedReservationRetainsHistory applied).1
    rw [root]
    exact sharedReservationPreservesRootCap _ _ _ _ _ _ applied
  | revoked id => exact prior
  | unchanged => exact prior

theorem sharedReservationHasUnrevokedLineage {mandate : Mandate}
    (applied : before.reserve revision steps offer purchase = some after)
    (member : mandate ∈ before.root :: steps.map (·.child)) :
    mandate.mandateId ∉ before.revokedMandateIds := by
  unfold SharedBudget.reserve at applied
  split at applied <;> simp_all
  split at applied <;> simp_all
  rcases applied with ⟨_, admitted, rfl⟩
  unfold SharedBudget.admitsLineage at admitted
  simp only [Bool.and_eq_true] at admitted
  have live := List.all_eq_true.mp admitted.1 mandate (by simpa using member)
  simp only [Bool.and_eq_true] at live
  simpa [List.contains_eq_mem] using live.1.1.2

/-- Any ancestor revoked in the historical anchor remains unusable for a fresh
reservation, even after unrelated sibling reservations and owner observations. -/
theorem SharedBudget.revoked_ancestor_blocks_run {mandate : Mandate} {revision : Nat}
    (framework : CedarPooSpec.ZeroTrust.Framework E SharedBudget)
    (run : CedarPooSpec.ZeroTrust.Run framework (Step E) original current)
    (revoked : mandate.mandateId ∈ original.revokedMandateIds)
    (member : mandate ∈ current.root :: steps.map (·.child)) :
    current.reserve revision steps offer purchase = none := by
  cases result : current.reserve revision steps offer purchase with
  | none => rfl
  | some after =>
    exact False.elim (sharedReservationHasUnrevokedLineage result member
      ((run_retains framework run).2.2.1 _ revoked))

open LeanPoo.Functional.DeclarativeMetadata

/-- Proposal inputs are not a durable commit or a permission to dispatch. -/
structure SharedBudget.ReservationInput where
  state : SharedBudget
  expectedRevision : Nat
  steps : List Delegation
  offer : MerchantOffer
  purchase : Purchase

/-- The Contract binds the exact existing allocator, rather than independently
asserting verified flags or supplying a second reservation implementation. -/
def SharedBudget.reservationContract : Contract Unit ReservationInput SharedBudget where
  input := ⟨"current-shared-root-and-delegation", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"exact-shared-reservation-proposal", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result =>
    input.state.reserve input.expectedRevision input.steps input.offer input.purchase = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def SharedBudget.prepareReservation (input : ReservationInput) :
    Except String (SharedBudget × Unit) :=
  match input.state.reserve input.expectedRevision input.steps input.offer input.purchase with
  | some result => .ok (result, ())
  | none => .error "Shared reservation refused"

theorem SharedBudget.reservation_receipt_retains
    (receipt : Invocation reservationContract prepareReservation input) :
    input.state.retains receipt.result :=
  sharedReservationRetainsHistory receipt.logic

theorem SharedBudget.reservation_receipt_root_cap
    (receipt : Invocation reservationContract prepareReservation input) :
    receipt.result.spentMinor ≤ input.state.root.totalCap :=
  sharedReservationPreservesRootCap _ _ _ _ _ _ receipt.logic

theorem SharedBudget.reservation_receipt_lineage_unique
    (receipt : Invocation reservationContract prepareReservation input) :
    (input.state.root.mandateId :: input.steps.map (·.child.mandateId)).Nodup ∧
    (input.state.root.agentId :: input.steps.map (·.child.agentId)).Nodup ∧
    (input.state.root.agentPublicKey :: input.steps.map (·.child.agentPublicKey)).Nodup := by
  have accepted := receipt.logic
  change input.state.reserve input.expectedRevision input.steps input.offer input.purchase =
    some receipt.result at accepted
  cases resolved : Delegation.resolveChain input.state.root input.steps with
  | none => simp [SharedBudget.reserve, resolved] at accepted
  | some final => exact Delegation.resolvedLineageUnique resolved

end CedarPooSpec.AgenticAI.Commerce
