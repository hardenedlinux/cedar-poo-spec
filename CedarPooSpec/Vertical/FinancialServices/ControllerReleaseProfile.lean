import CedarPooSpec.Vertical.FinancialServices.ControllerRelease
import LeanPoo.Object.Dataflow
import CedarPooSpec.Functional.ObjectProfile

/-! Controller-owned release settings and their inherited Cedar policy.
Changing a threshold does not replace the controller or senior approver slots. -/
namespace CedarPooSpec.Vertical.FinancialServices.ControllerReleaseProfile
open LeanPoo.Object.Dataflow (Expr)

open Cedar.Spec LeanPoo
open LeanPoo.Object.Dataflow.Builder

inductive Key where
  | template
  | threshold | controllerGroup | seniorGroup | control | policy
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .template => ControllerRelease
  | .threshold => String
  | .controllerGroup | .seniorGroup => EntityUID
  | .control => ControllerRelease
  | .policy => Policy

abbrev Object := LeanPoo.Object.Dataflow.Instance Key Value

def define (name : String) (initial : ControllerRelease) : Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  LeanPoo.Object.Dataflow.define name do
    LeanPoo.Object.Dataflow.Builder.value .template initial
    value .threshold initial.threshold
    value .controllerGroup initial.controllerGroup
    value .seniorGroup initial.seniorGroup
    derived .control
      ((fun threshold controllerGroup seniorGroup => { initial with threshold, controllerGroup, seniorGroup })
        <$> Expr.need (Value := Value) .threshold
        <*> Expr.need (Value := Value) .controllerGroup
        <*> Expr.need (Value := Value) .seniorGroup)
    derived .policy (ControllerRelease.bounded
        <$> Expr.need (Value := Value) .control)

def withThreshold (parent : Object) (name threshold : String) : Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  parent.extendWith name do value .threshold threshold

open LeanPoo.Functional.ObjectContract

private def shape : Contract Object Key Unit String :=
  Functional.ObjectProfile.shape [.template, .threshold, .controllerGroup, .seniorGroup, .control, .policy]
/-- Use Cedar's decimal parser for threshold admission, and require a positive
amount. Static String typing alone cannot establish this industry contract. -/
def contract : Contract Object Key Unit String :=
  refine shape fun profile path =>
    match profile.read .control, profile.read .policy with
    | some control, some policy =>
        let threshold := match Cedar.Spec.Ext.Decimal.decimal control.threshold with
          | none => [.rejected (path ++ [.threshold]) "invalid decimal threshold"]
          | some amount =>
              if amount.toInt > 0 then [] else [.rejected (path ++ [.threshold]) "nonpositive threshold"]
        let templateAligned := match profile.read .template with
          | none => false
          | some template => decide (control = { template with
              threshold := control.threshold, controllerGroup := control.controllerGroup, seniorGroup := control.seniorGroup })
        let aligned := templateAligned = true ∧ profile.read .threshold = some control.threshold ∧
          profile.read .controllerGroup = some control.controllerGroup ∧
          profile.read .seniorGroup = some control.seniorGroup ∧ policy = control.bounded
        threshold ++ (if aligned then [] else [.rejected path "controller projection mismatch"])
    | _, _ => [.rejected path "missing controller projection"]

def issues (profile : Object) : List (Issue Key String) := diagnose contract profile []

def control? (profile : Object) : Option ControllerRelease :=
  Functional.ObjectProfile.read contract profile .control

def policy? (profile : Object) : Option Policy :=
  Functional.ObjectProfile.read contract profile .policy

theorem policy_requires_contract (profile : Object) (policy : Policy)
    (accepted : policy? profile = some policy) : diagnose contract profile [] = [] :=
  Functional.ObjectProfile.read_requires_contract contract profile _ _ accepted

end CedarPooSpec.Vertical.FinancialServices.ControllerReleaseProfile
