import CedarPooSpec.ZeroTrust

namespace CedarPooSpec.ZeroTrust.UsageControlTest

structure View where
  epoch : Nat
  consumed : Bool
  unknown : Bool
  posture : Bool
  obligationCount : Nat
  deriving DecidableEq

def initial : View := ⟨0, true, true, true, 0⟩
def core : Framework Unit View where
  authenticated := fun _ => True
  authorized := fun _ _ => True
  currentAtUse := fun v => v.epoch = 0
  consumptionCommitted := fun _ v => v.consumed = true
  unknownRetained := fun _ v => v.unknown = true
  revoked := fun _ _ => False
  mediated := fun _ _ => True

def control : UsageControl Unit View where
  core := core
  authorization := fun _ _ _ => True
  condition := fun _ _ v => v.posture = true
  obligation := fun _ _ before after => after.obligationCount = before.obligationCount + 1
  mutation := fun _ _ before after => after.consumed = before.consumed ∧ after.unknown = before.unknown
  recovery := fun before after => after.consumed = before.consumed ∧ after.unknown = before.unknown
  terminal := fun _ => True
  accounted := fun v => v.unknown = false

def raw (_ : View) (_ : Option Unit) (_ : View) : Prop := True
def next : View := { initial with obligationCount := 1 }

theorem witnessed_use : control.step .ongoing raw initial () next := by
  simp [UsageControl.step, MediatedStep, Framework.required, control, core, raw, next, initial]

-- Authentication and Allow alone omit both posture and witnessed obligations.
theorem allow_only_counterexample :
    core.required () {initial with posture := false} ∧
      ¬ control.step .ongoing raw {initial with posture := false} () next := by
  constructor
  · simp [Framework.required, core, initial]
  · exact missing_condition_blocks control (by simp [control])

theorem obligation_promise_is_not_performance : ¬ control.step .ongoing raw initial () initial :=
  missing_obligation_blocks control (by simp [control, initial])

theorem mutable_consumption_cannot_reset :
    ¬ control.step .ongoing raw initial () {next with consumed := false} := by
  intro accepted
  have preserved := usage_requires_mutation control accepted
  simp [control, initial] at preserved

theorem recovery_is_not_reauthorization :
    control.resume initial {initial with epoch := 1} ∧
      ¬ control.step .ongoing raw {initial with epoch := 1} () next := by
  constructor
  · simp [UsageControl.resume, control]
  · intro accepted
    have admitted := usage_retains_core control accepted
    simp [Framework.required, control, core] at admitted

theorem terminal_alone_cannot_release_unknown :
    control.terminal initial ∧ ¬ control.close initial :=
  ⟨True.intro, unknown_accounting_blocks_close control (by simp [control, initial])⟩

#print axioms usage_rechecks_after_recovery
#print axioms witnessed_use
#print axioms allow_only_counterexample
#print axioms recovery_is_not_reauthorization
end CedarPooSpec.ZeroTrust.UsageControlTest
