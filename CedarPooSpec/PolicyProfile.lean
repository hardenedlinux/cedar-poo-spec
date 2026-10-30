import Cedar.Spec.Policy
import LeanPoo.Object.Dataflow
import CedarPooSpec.Functional.ObjectProfile

/-! A typed LeanPOO profile for one Cedar policy owner. The setting is the
direct slot; the policy is an inherited computation over final self. Revising
the setting retains the parent object and regenerates only this policy. -/

namespace CedarPooSpec.PolicyProfile
open LeanPoo.Object.Dataflow (Expr)

open Cedar.Spec LeanPoo

inductive Key where
  | setting
  | render
  | policy
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value (Setting : Type) : Key → Type
  | .setting => Setting
  | .render => Setting → Policy
  | .policy => Policy

abbrev Object (Setting : Type) := LeanPoo.Object.Dataflow.Instance Key (Value Setting)

def define {Setting : Type} (name : String) (initial : Setting)
    (render : Setting → Policy) : Except (LeanPoo.Object.Dataflow.Error Key) (Object Setting) :=
  LeanPoo.Object.Dataflow.define name do
    LeanPoo.Object.Dataflow.Builder.value .setting initial
    LeanPoo.Object.Dataflow.Builder.value .render render
    LeanPoo.Object.Dataflow.Builder.derived .policy
      ((fun setting selected => selected setting)
        <$> Expr.need (Value := Value Setting) .setting
        <*> Expr.need (Value := Value Setting) .render)

def revise {Setting : Type} (parent : Object Setting)
    (name : String) (setting : Setting) :
    Except (LeanPoo.Object.Dataflow.Error Key) (Object Setting) :=
  parent.extendWith name do
    LeanPoo.Object.Dataflow.Builder.value .setting setting

open LeanPoo.Functional.ObjectContract

private def shape {Setting : Type} : Contract (Object Setting) Key Unit String :=
  Functional.ObjectProfile.shape [.setting, .render, .policy]
/-- Check actual inherited settings, callback and produced Cedar policy. Function
values are never compared; the selected callback's actual output is checked. -/
def contract {Setting : Type} : Contract (Object Setting) Key Unit String :=
  refine shape fun profile path =>
    match profile.read .setting, profile.read .render, profile.read .policy with
    | some setting, some render, some policy =>
      if policy == render setting then [] else [.rejected path "policy projection mismatch"]
    | _, _, _ => [.rejected path "missing policy projection"]

def issues {Setting : Type} (profile : Object Setting) := diagnose contract profile []

def policy? {Setting : Type} (profile : Object Setting) : Option Policy :=
  Functional.ObjectProfile.read contract profile .policy

theorem policy_requires_contract {Setting : Type} (profile : Object Setting) (policy : Policy)
    (accepted : policy? profile = some policy) : diagnose contract profile [] = [] :=
  Functional.ObjectProfile.read_requires_contract contract profile _ _ accepted

end CedarPooSpec.PolicyProfile
