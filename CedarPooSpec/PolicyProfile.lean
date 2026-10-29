import Cedar.Spec.Policy
import LeanPoo.Object.Definition
import CedarPooSpec.Functional.ObjectProfile

/-! A typed LeanPOO profile for one Cedar policy owner. The setting is the
direct slot; the policy is an inherited computation over final self. Revising
the setting retains the parent object and regenerates only this policy. -/

namespace CedarPooSpec.PolicyProfile

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

abbrev Object (Setting : Type) := LeanPoo.Object.Memoized Key (Value Setting)

def define {Setting : Type} (name : String) (initial : Setting)
    (render : Setting → Policy) : Except C4.Error (Object Setting) :=
  LeanPoo.Object.define name do
    LeanPoo.Object.Declaration.Builder.value .setting initial
    LeanPoo.Object.Declaration.Builder.value .render render
    LeanPoo.Object.Declaration.Builder.slot .policy
      (.self fun self => do
        let setting ← self .setting
        let selected ← self .render
        pure (selected setting))

def revise {Setting : Type} (parent : Object Setting)
    (name : String) (setting : Setting) :
    Except C4.Error (Object Setting) :=
  parent.extendWith name do
    LeanPoo.Object.Declaration.Builder.value .setting setting

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
