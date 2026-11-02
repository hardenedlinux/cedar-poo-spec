import CedarPooSpec.Vertical.FinancialServices.BankingToolOwner
import LeanPoo.Object.Dataflow
import CedarPooSpec.Functional.ObjectProfile

/-! A typed prototype for one banking tool owner. The parent keeps its
original action list; an inherited slot rebuilds the owner from final self. -/

namespace CedarPooSpec.Vertical.FinancialServices.BankingToolProfile
open LeanPoo.Object.Dataflow (Expr)

open Cedar.Spec LeanPoo

inductive Key where
  | template
  | actions
  | owner
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .template => BankingToolOwner
  | .actions => List EntityUID
  | .owner => BankingToolOwner

abbrev Object := LeanPoo.Object.Dataflow.Instance Key Value

def define (name : String) (initial : BankingToolOwner) :
    Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  LeanPoo.Object.Dataflow.define name do
    LeanPoo.Object.Dataflow.Builder.value .template initial
    LeanPoo.Object.Dataflow.Builder.value .actions initial.actions
    LeanPoo.Object.Dataflow.Builder.derived .owner
      ((fun actions => { initial with actions })
        <$> Expr.need (Value := Value) .actions)

def onActions (parent : Object) (name : String) (actions : List EntityUID) :
    Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  parent.extendWith name do
    LeanPoo.Object.Dataflow.Builder.value .actions actions

open LeanPoo.Functional.ObjectContract

def contract : Contract Object Key Unit String :=
  refine (Functional.ObjectProfile.shape [.template, .actions, .owner]) fun profile path =>
    match profile.read .template, profile.read .actions, profile.read .owner with
    | some template, some actions, some owner =>
      if owner = { template with actions } then []
      else [.rejected path "banking owner projection mismatch"]
    | _, _, _ => [.rejected path "missing banking owner projection"]

def issues (profile : Object) := diagnose contract profile []

def owner? (profile : Object) : Option BankingToolOwner :=
  Functional.ObjectProfile.read contract profile .owner

theorem owner_requires_contract (profile : Object) (value : BankingToolOwner)
    (accepted : owner? profile = some value) : diagnose contract profile [] = [] :=
  Functional.ObjectProfile.read_requires_contract contract profile _ _ accepted

end CedarPooSpec.Vertical.FinancialServices.BankingToolProfile
