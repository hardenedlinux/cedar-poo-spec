import CedarPooSpec.ZeroTrust.Continuous

/-! A functional UCON-inspired safety adapter over an application's existing
transition relation. No scheduler, identity service or Gateway types live here.
Obligations are witnessed actions across states, not promises encoded as Allow.
Post-use accounting is an application extension, not a claim about all UCON rules. -/
namespace CedarPooSpec.ZeroTrust

inductive UsePhase where
  | initial | ongoing
  deriving DecidableEq

structure UsageControl (E V : Type) where
  core : Framework E V
  authorization : UsePhase → Requirement E V
  condition : UsePhase → Requirement E V
  obligation : UsePhase → E → V → V → Prop
  mutation : UsePhase → E → V → V → Prop
  recovery : V → V → Prop
  terminal : V → Prop
  accounted : V → Prop

/-- Checks at the actual source state, and witnessed obligation/mutation at the
actual transition. Admission of a new effect always retains core consumption. -/
def UsageControl.step (control : UsageControl E V) (phase : UsePhase)
    (transition : V → Option E → V → Prop) (before : V) (effect : E) (after : V) : Prop :=
  MediatedStep control.core transition before (some effect) after ∧
    control.authorization phase effect before ∧ control.condition phase effect before ∧
    control.obligation phase effect before after ∧ control.mutation phase effect before after

/-- Recovery may change the observation and owner. Only the supplied relation
may decide whether original consumption and unresolved obligations survive. -/
def UsageControl.resume (control : UsageControl E V) (before after : V) : Prop :=
  control.recovery before after

/-- Accounting closure permits no effect by itself. Unknown exposure must be
excluded by the application's terminal/accounted interpretations. -/
def UsageControl.close (control : UsageControl E V) (view : V) : Prop :=
  control.terminal view ∧ control.accounted view

theorem usage_retains_core (control : UsageControl E V)
    (accepted : control.step phase transition before effect after) :
    control.core.required effect before := accepted.1.2 effect rfl

theorem missing_condition_blocks (control : UsageControl E V)
    (missing : ¬ control.condition phase effect before) :
    ¬ control.step phase transition before effect after := fun accepted => missing accepted.2.2.1

theorem missing_obligation_blocks (control : UsageControl E V)
    (missing : ¬ control.obligation phase effect before after) :
    ¬ control.step phase transition before effect after := fun accepted => missing accepted.2.2.2.1

theorem usage_requires_mutation (control : UsageControl E V)
    (accepted : control.step phase transition before effect after) :
    control.mutation phase effect before after := accepted.2.2.2.2

theorem usage_rechecks_after_recovery (control : UsageControl E V)
    (_recovered : control.resume old before)
    (accepted : control.step .ongoing transition before effect after) :
    control.core.currentAtUse before ∧ control.core.consumptionCommitted effect before ∧
      control.core.unknownRetained effect before := by
  have current := usage_retains_core control accepted
  exact ⟨current.2.2.1, current.2.2.2.1, current.2.2.2.2.1⟩

theorem unknown_accounting_blocks_close (control : UsageControl E V)
    (unknown : ¬ control.accounted view) : ¬ control.close view := fun closed => unknown closed.2

end CedarPooSpec.ZeroTrust
