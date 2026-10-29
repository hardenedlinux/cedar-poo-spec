import CedarPooSpec.Vertical.FinancialServices.BankingToolOwner
import LeanPoo.Object.Definition
import CedarPooSpec.Functional.ObjectProfile

/-! A typed prototype for one banking tool owner. The parent keeps its
original action list; an inherited slot rebuilds the owner from final self. -/

namespace CedarPooSpec.Vertical.FinancialServices.BankingToolProfile

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

abbrev Object := LeanPoo.Object.Memoized Key Value

def define (name : String) (initial : BankingToolOwner) :
    Except C4.Error Object :=
  LeanPoo.Object.define name do
    LeanPoo.Object.Declaration.Builder.value .template initial
    LeanPoo.Object.Declaration.Builder.value .actions initial.actions
    LeanPoo.Object.Declaration.Builder.slot .owner
      (.self fun self =>
        (self .actions).map fun actions => { initial with actions })

def onActions (parent : Object) (name : String) (actions : List EntityUID) :
    Except C4.Error Object :=
  parent.extendWith name do
    LeanPoo.Object.Declaration.Builder.value .actions actions

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
