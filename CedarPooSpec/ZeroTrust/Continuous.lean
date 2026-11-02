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


/-- Pure specification of an authority-owned compare-and-advance operation.
The transition receives the actual attributes, never a cached assessment. All
relevant writers must advance this non-reused generation. A native Host must
read, check and install under one atomic boundary; this function performs no IO. -/
def Observation.compareAndAdvance (expectedGeneration : Nat) (actual : Observation A)
    (stale : Error) (transition : A → Except Error (Result × A)) :
    Except Error (Result × Observation A) :=
  if actual.generation != expectedGeneration then .error stale else
  match transition actual.attributes with
  | .error error => .error error
  | .ok (result, next) => .ok (result, ⟨actual.generation + 1, next⟩)

theorem Observation.compareAndAdvance_stale (expectedGeneration : Nat) (actual : Observation A)
    (stale : Error) (transition : A → Except Error (Result × A))
    (changed : actual.generation ≠ expectedGeneration) :
    compareAndAdvance expectedGeneration actual stale transition = .error stale := by
  simp [compareAndAdvance, changed]

theorem Observation.compareAndAdvance_error (expectedGeneration : Nat) (actual : Observation A)
    (stale error : Error) (transition : A → Except Error (Result × A))
    (same : actual.generation = expectedGeneration)
    (failed : transition actual.attributes = .error error) :
    compareAndAdvance expectedGeneration actual stale transition = .error error := by
  simp [compareAndAdvance, same, failed]

/-- Success retains the exact actual-state transition and its successor cut.
Authentication and the authority's serialization are not inferred from equality. -/
theorem Observation.compareAndAdvance_postcondition (expectedGeneration : Nat) (actual : Observation A)
    (stale : Error) (transition : A → Except Error (Result × A))
    (result : Result) (next : Observation A)
    (accepted : compareAndAdvance expectedGeneration actual stale transition = .ok (result, next)) :
    actual.generation = expectedGeneration ∧
      transition actual.attributes = .ok (result, next.attributes) ∧
      next.generation = actual.generation + 1 := by
  by_cases same : actual.generation = expectedGeneration
  · cases advanced : transition actual.attributes with
    | error error => simp [compareAndAdvance, same, advanced] at accepted
    | ok pair =>
      obtain ⟨value, attributes⟩ := pair
      simp [compareAndAdvance, same, advanced] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact ⟨same, rfl, by simp [same]⟩
  · simp [compareAndAdvance, same] at accepted

/-- A previously captured cut cannot be revived by restoring equal attributes
or changing the checked callback after a successful compare-and-advance. -/
theorem Observation.returned_cut_refuses_reuse (expectedGeneration : Nat) (actual : Observation A)
    (stale : Error) (transition : A → Except Error (Result × A))
    (result : Result) (next : Observation A)
    (accepted : compareAndAdvance expectedGeneration actual stale transition = .ok (result, next))
    (otherStale : OtherError) (otherTransition : A → Except OtherError (OtherResult × A)) :
    compareAndAdvance expectedGeneration next otherStale otherTransition = .error otherStale := by
  obtain ⟨same, _, successor⟩ := compareAndAdvance_postcondition _ _ _ _ _ _ accepted
  apply compareAndAdvance_stale
  omega

/-- Bind a successful current transition to the existing mediated-step meaning.
The application's checked transition law remains explicit. -/
theorem Observation.compareAndAdvance_retains_framework
    (expectedGeneration : Nat) (actual : Observation V) (stale : Error)
    (transition : V → Except Error (Result × V)) (result : Result) (next : Observation V)
    (accepted : compareAndAdvance expectedGeneration actual stale transition = .ok (result, next))
    (checked : ∀ before output after, transition before = .ok (output, after) →
      MediatedStep framework step before (some effect) after) :
    framework.required effect actual.attributes ∧ step actual.attributes (some effect) next.attributes := by
  have current := (compareAndAdvance_postcondition _ _ _ _ _ _ accepted).2.1
  have mediated := checked _ _ _ current
  exact ⟨mediated.2 effect rfl, mediated.1⟩

/-- Reuse the application's existing run, including non-effect controls and
recovery. Monotonicity must hold for every actual writer, not only publication. -/
theorem run_generation_monotone (read : V → Observation A)
    (monotone : ∀ before effect after, step before effect after →
      (read before).generation ≤ (read after).generation)
    (run : Run framework step first last) :
    (read first).generation ≤ (read last).generation := by
  exact run_preserves (fun view => (read first).generation ≤ (read view).generation)
    (fun before effect after event prior => Nat.le_trans prior (monotone before effect after event))
    (Nat.le_refl _) run

/-- Retirement survives any finite forward run, with arbitrary callbacks and
restored attributes. This does not infer monotonic recovery from a mutex. -/
theorem Observation.retired_cut_refuses_after_run (read : V → Observation A)
    (generation : Nat)
    (monotone : ∀ before effect after, step before effect after →
      (read before).generation ≤ (read after).generation)
    (run : Run framework step first last)
    (retired : generation < (read first).generation)
    (stale : Error) (transition : A → Except Error (Result × A)) :
    compareAndAdvance generation (read last) stale transition = .error stale := by
  have forward := run_generation_monotone read monotone run
  apply compareAndAdvance_stale
  omega

end CedarPooSpec.ZeroTrust
