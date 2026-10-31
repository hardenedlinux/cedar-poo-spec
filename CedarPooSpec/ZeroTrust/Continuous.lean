import CedarPooSpec.ZeroTrust.Composition

namespace CedarPooSpec.ZeroTrust

def observedAt (read : V → Observation A) (observation : Observation A) : Requirement E V :=
  fun _ view => observation = read view

def Framework.atObservation (framework : Framework E V) (read : V → Observation A)
    (observation : Observation A) : Framework E V :=
  framework.withRequirement (observedAt read observation)

theorem changed_observation_blocks (framework : Framework E V) (read : V → Observation A)
    (observation : Observation A) (changed : observation ≠ read view) :
    ¬ (framework.atObservation read observation).required effect view :=
  fun accepted => changed accepted.2.1.2

theorem changed_generation_blocks (framework : Framework E V) (read : V → Observation A)
    (observation : Observation A) (changed : observation.generation ≠ (read view).generation) :
    ¬ (framework.atObservation read observation).required effect view := by
  apply changed_observation_blocks framework read observation
  exact fun same => changed (congrArg Observation.generation same)

theorem revoked_blocks (framework : Framework E V) (revoked : framework.revoked effect view) :
    ¬ framework.required effect view := fun accepted => accepted.2.2.2.2.2.1 revoked

theorem unknown_commit_blocks (framework : Framework E V)
    (unknown : ¬ framework.consumptionCommitted effect view) :
    ¬ framework.required effect view := fun accepted => unknown accepted.2.2.2.1

/-- A trace contract over an application's existing transition relation. This
adds no second state machine, ledger or scheduler. Some marks one new effect;
none includes observations, mutation, recovery and already admitted buffer drain. -/
def MediatedStep (framework : Framework E V) (step : V → Option E → V → Prop)
    (before : V) (effect : Option E) (after : V) : Prop :=
  step before effect after ∧ ∀ e, effect = some e → framework.required e before

inductive Run (framework : Framework E V) (step : V → Option E → V → Prop) : V → V → Prop where
  | refl (view) : Run framework step view view
  | next : Run framework step a b → MediatedStep framework step b effect c →
      Run framework step a c

theorem effect_step_rechecks (event : MediatedStep framework step before (some effect) after) :
    framework.currentAtUse before ∧ framework.authorized effect before ∧
    framework.consumptionCommitted effect before ∧ ¬ framework.revoked effect before := by
  have admitted := event.2 effect rfl
  exact ⟨admitted.2.2.1, admitted.2.1, admitted.2.2.2.1, admitted.2.2.2.2.2.1⟩

theorem revoked_state_cannot_emit (revoked : framework.revoked effect before) :
    ¬ MediatedStep framework step before (some effect) after :=
  fun event => revoked_blocks framework revoked (event.2 effect rfl)

/-- Projection onto any existing application invariant, including persisted
consumption and unknown holds. The application supplies its real step law. -/
theorem run_preserves (invariant : V → Prop)
    (preserve : ∀ before effect after, step before effect after →
      invariant before → invariant after)
    (initial : invariant a) (run : Run framework step a b) : invariant b := by
  induction run with
  | refl => exact initial
  | next prior event ih => exact preserve _ _ _ event.1 ih


end CedarPooSpec.ZeroTrust
