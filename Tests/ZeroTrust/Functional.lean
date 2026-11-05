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

-- Equal attributes after an ABA do not revive the authority's old cut.
example : Observation.compareAndAdvance 0 (snapshot restored) "stale"
    (fun _ => (.error "callback must not run" : Except String (Unit × Bool))) = .error "stale" := rfl
example : Observation.compareAndAdvance 2 (snapshot restored) "stale"
    (fun allowed => (.ok ((), allowed) : Except String (Unit × Bool))) = .ok ((), ⟨3, true⟩) := rfl
example : Observation.compareAndAdvance 2 (snapshot restored) "stale"
    (fun _ => (.error "denied" : Except String (Unit × Bool))) = .error "denied" := rfl

-- Pure checks against two copies of the same pre-state both succeed. The
-- native authority must serialize the read/check/install, not cache this result.
#guard (Observation.compareAndAdvance 0 (snapshot initial) "stale"
    (fun allowed => (.ok ((), allowed) : Except String (Unit × Bool)))).isOk &&
  (Observation.compareAndAdvance 0 (snapshot initial) "stale"
    (fun allowed => (.ok ((), allowed) : Except String (Unit × Bool)))).isOk

#print axioms Observation.compareAndAdvance_error
#print axioms Observation.compareAndAdvance_postcondition
#print axioms Observation.returned_cut_refuses_reuse
#print axioms Observation.compareAndAdvance_retains_framework

-- Arbitrarily many application controls may intervene. The premise is about
-- the real step relation, including recovery, rather than a bounded corpus.
theorem monotone_recovery_keeps_old_cut_retired
    (history : Run framework (fun before _ after => before.generation ≤ after.generation)
      restored final) :
    Observation.compareAndAdvance 0 (snapshot final) "stale"
      (fun allowed => (.ok ((), allowed) : Except String (Unit × Bool))) = .error "stale" := by
  apply Observation.retired_cut_refuses_after_run snapshot 0 (fun _ _ _ event => event) history
  decide

-- A mediated no-effect edge alone does not establish monotonic recovery.
theorem authority_rollback_revives_cut_counterexample :
    Run framework rawStep restored initial ∧
      (Observation.compareAndAdvance 0 (snapshot initial) "stale"
        (fun allowed => (.ok ((), allowed) : Except String (Unit × Bool)))).isOk = true := by
  constructor
  · exact .next (effect := none) (.refl restored)
      ⟨True.intro, by intro effect impossible; cases impossible⟩
  · rfl

#print axioms run_generation_monotone
#print axioms Observation.retired_cut_refuses_after_run
#print axioms monotone_recovery_keeps_old_cut_retired
#print axioms authority_rollback_revives_cut_counterexample
end CedarPooSpec.ZeroTrustTest


namespace CedarPooSpec.ZeroTrust.TransitionSafetyTest

inductive State where
  | ready | armed | violated
  deriving DecidableEq

inductive Action where
  | arm | emit | sample
  deriving DecidableEq

def safe (state : State) : Prop := state ≠ .violated

-- Both policy versions are identical. Authorization non-expansion alone says
-- nothing about the state reached after a sequence of permitted effects.
def unchangedPolicy : Framework Action State where
  authenticated := fun _ => True
  authorized := fun _ _ => True
  currentAtUse := fun _ => True
  consumptionCommitted := fun _ _ => True
  unknownRetained := fun _ _ => True
  revoked := fun _ _ => False
  mediated := fun _ _ => True

def step (before : State) (effect : Option Action) (after : State) : Prop :=
  match effect with
  | none => after = before
  | some .arm => after = .armed
  | some .emit => after = if before = .armed then .violated else .ready
  | some .sample => after = .ready ∨ after = .violated

theorem identical_authorization_can_reach_unsafe :
    Run unchangedPolicy step .ready .violated := by
  have first : MediatedStep unchangedPolicy step .ready (some .arm) .armed := by
    simp [MediatedStep, step, Framework.required, unchangedPolicy]
  have second : MediatedStep unchangedPolicy step .armed (some .emit) .violated := by
    simp [MediatedStep, step, Framework.required, unchangedPolicy]
  exact Run.next (Run.next (.refl State.ready) first) second

theorem pointwise_refinement_does_not_imply_trace_safety :
    Refines unchangedPolicy.required unchangedPolicy.required ∧
      Run unchangedPolicy step .ready .violated ∧ ¬ safe .violated :=
  ⟨fun _ _ accepted => accepted, identical_authorization_can_reach_unsafe, by simp [safe]⟩

theorem harmless_first_step_allowed :
    (unchangedPolicy.atInvariant step safe).required .arm .ready := by
  simp [Framework.atInvariant, Framework.withRequirement, Framework.required,
    strengthen, preservesInvariant, step, safe, unchangedPolicy]

theorem newly_dangerous_second_step_refused :
    ¬ (unchangedPolicy.atInvariant step safe).required .emit .armed := by
  apply unsafe_successor_blocks unchangedPolicy step safe (after := .violated)
  · simp [step]
  · simp [safe]

-- One favorable sample is insufficient when another actual successor is bad.
theorem safe_sample_does_not_certify_nondeterminism :
    step .ready (some .sample) .ready ∧
      ¬ (unchangedPolicy.atInvariant step safe).required .sample .ready := by
  constructor
  · simp [step]
  · apply unsafe_successor_blocks unchangedPolicy step safe (after := .violated)
    · simp [step]
    · simp [safe]

-- Preservation as an implication would be vacuous in an already unsafe
-- observed state. A new effect must establish source safety as well.
theorem unsafe_observed_state_refused :
    ¬ (unchangedPolicy.atInvariant step safe).required .arm .violated := by
  apply unsafe_source_blocks unchangedPolicy step safe
  simp [safe]

theorem vacuous_preservation_is_insufficient :
    (∀ after, step .violated (some .arm) after → safe .violated → safe after) ∧
      ¬ (unchangedPolicy.atInvariant step safe).required .arm .violated := by
  constructor
  · simp [safe]
  · exact unsafe_observed_state_refused

theorem all_guarded_runs_safe
    (run : Run (unchangedPolicy.atInvariant step safe) step .ready after) : safe after := by
  apply invariant_guard_preserves_run unchangedPolicy step safe _ (by simp [safe]) run
  intro before after maintenance initial
  simp only [step] at maintenance
  simpa [maintenance] using initial

def rollbackStep (before : State) (effect : Option Action) (after : State) : Prop :=
  match effect with
  | none => after = .violated
  | some action => step before (some action) after

-- The guard never turns an unproved recovery or fact-update edge into a safe one.
theorem unchecked_maintenance_can_break_safety :
    Run (unchangedPolicy.atInvariant rollbackStep safe) rollbackStep .ready .violated := by
  have event : MediatedStep (unchangedPolicy.atInvariant rollbackStep safe)
      rollbackStep .ready none .violated := by simp [MediatedStep, rollbackStep]
  exact Run.next (.refl State.ready) event

#print axioms run_preserves_mediated
#print axioms invariant_guard_preserves_framework
#print axioms unsafe_successor_blocks
#print axioms unsafe_source_blocks
#print axioms invariant_guard_effect_states
#print axioms unsafe_observed_state_refused
#print axioms vacuous_preservation_is_insufficient
#print axioms invariant_guard_preserves_run
#print axioms pointwise_refinement_does_not_imply_trace_safety
#print axioms identical_authorization_can_reach_unsafe
#print axioms all_guarded_runs_safe
#print axioms unchecked_maintenance_can_break_safety

end CedarPooSpec.ZeroTrust.TransitionSafetyTest
