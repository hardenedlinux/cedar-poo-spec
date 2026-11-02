import CedarPooSpec.ZeroTrust

/-! Generic artifact access fixture: no Gateway, Cedar request or operation
ledger types. These predicates model a trusted adapter, not deployed facts. -/
namespace CedarPooSpec.ZeroTrustTest
open ZeroTrust

structure View where
  generation : Nat
  allowed : Bool
  revoked : Bool
  consumed : Bool
  held : Nat
  deriving DecidableEq

def initial : View := ⟨0, true, false, true, 4⟩
def revoked : View := { initial with generation := 1, allowed := false, revoked := true }
def restored : View := { initial with generation := 2 }
def snapshot (view : View) : Observation Bool := ⟨view.generation, view.allowed⟩
def framework : Framework Unit View where
  authenticated := fun _ => True
  authorized := fun _ view => view.allowed = true
  currentAtUse := fun _ => True
  consumptionCommitted := fun _ view => view.consumed = true
  unknownRetained := fun _ view => view.held = 4
  revoked := fun _ view => view.revoked = true
  mediated := fun _ _ => True

theorem first_use_permitted : framework.required () initial := by
  simp [Framework.required, framework, initial]

-- Even a supplied currentAtUse proof and an old Allow do not defeat revocation.
theorem currentness_alone_cannot_override_revocation :
    framework.currentAtUse revoked ∧ ¬ framework.required () revoked :=
  ⟨True.intro, revoked_blocks framework rfl⟩

theorem restored_attributes_do_not_revive_old_observation :
    ¬ (framework.atObservation snapshot (snapshot initial)).required () restored := by
  apply changed_generation_blocks
  decide

theorem fresh_observation_can_progress_without_reconsuming :
    (framework.atObservation snapshot (snapshot restored)).required () restored := by
  simp [Framework.atObservation, Framework.withRequirement, strengthen,
    Framework.required, framework, observedAt, restored, initial]

theorem lost_consumption_cannot_send :
    ¬ framework.required () {initial with consumed := false} := by
  apply unknown_commit_blocks
  simp [framework]

theorem revoke_then_recover_cannot_refund :
    ¬ framework.required () {restored with held := 0} := by
  simp [Framework.required, framework]

-- Removing the ongoing guard permits a raw effect edge from a revoked state.
-- The checked trace relation excludes that edge, irrespective of its target.
def rawStep (_ : View) (_ : Option Unit) (_ : View) : Prop := True
theorem omitted_ongoing_check_counterexample :
    rawStep revoked (some ()) revoked ∧
      ¬ MediatedStep framework rawStep revoked (some ()) revoked :=
  ⟨True.intro, revoked_state_cannot_emit rfl⟩

#print axioms with_requirement_preserves_framework
#print axioms run_preserves
#print axioms restored_attributes_do_not_revive_old_observation
#print axioms fresh_observation_can_progress_without_reconsuming
#print axioms omitted_ongoing_check_counterexample
end CedarPooSpec.ZeroTrustTest
