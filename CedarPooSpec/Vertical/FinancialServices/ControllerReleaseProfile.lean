import CedarPooSpec.Vertical.FinancialServices.ControllerRelease
import LeanPoo.Object.Definition
import LeanPoo.Functional.ObjectContractRefinement

/-! Controller-owned release settings and their inherited Cedar policy.
Changing a threshold does not replace the controller or senior approver slots. -/
namespace CedarPooSpec.Vertical.FinancialServices.ControllerReleaseProfile

open Cedar.Spec LeanPoo
open LeanPoo.Object.Declaration.Builder

inductive Key where
  | threshold | controllerGroup | seniorGroup | control | policy
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .threshold => String
  | .controllerGroup | .seniorGroup => EntityUID
  | .control => ControllerRelease
  | .policy => Policy

abbrev Object := LeanPoo.Object.Memoized Key Value

def define (name : String) (initial : ControllerRelease) : Except C4.Error Object :=
  LeanPoo.Object.define name do
    value .threshold initial.threshold
    value .controllerGroup initial.controllerGroup
    value .seniorGroup initial.seniorGroup
    slot .control (.self fun self => do
      let threshold ← self .threshold
      let controllerGroup ← self .controllerGroup
      let seniorGroup ← self .seniorGroup
      pure { initial with threshold, controllerGroup, seniorGroup })
    slot .policy (.self fun self => (self .control).map ControllerRelease.bounded)

def withThreshold (parent : Object) (name threshold : String) : Except C4.Error Object :=
  parent.extendWith name do value .threshold threshold

open LeanPoo.Functional.ObjectContract

private def shape : Contract Object Key Unit String where
  view := {
    isObject := fun _ => true
    prototype := fun _ => true
    names := fun profile => LeanPoo.allSlots profile.plan
    lookup := fun profile key => (profile.read key).map fun _ => () }
  fields := [.threshold, .controllerGroup, .seniorGroup, .control, .policy].map
    fun key => { name := key, check := fun _ _ => [] }
  strict := true
  constraints := []
  obligations := fun _ _ => []
  validInventory := Or.inl rfl

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
        let aligned := profile.read .threshold = some control.threshold ∧
          profile.read .controllerGroup = some control.controllerGroup ∧
          profile.read .seniorGroup = some control.seniorGroup ∧ policy = control.bounded
        threshold ++ (if aligned then [] else [.rejected path "controller projection mismatch"])
    | _, _ => [.rejected path "missing controller projection"]

def issues (profile : Object) : List (Issue Key String) := diagnose contract profile []

def control? (profile : Object) : Option ControllerRelease :=
  if (issues profile).isEmpty then profile.read .control else none

def policy? (profile : Object) : Option Policy :=
  if (issues profile).isEmpty then profile.read .policy else none

theorem policy_requires_contract (profile : Object) (policy : Policy)
    (accepted : policy? profile = some policy) : diagnose contract profile [] = [] := by
  unfold policy? at accepted
  split at accepted
  · simpa [issues, List.isEmpty_iff] using ‹(issues profile).isEmpty = true›
  · contradiction

end CedarPooSpec.Vertical.FinancialServices.ControllerReleaseProfile
