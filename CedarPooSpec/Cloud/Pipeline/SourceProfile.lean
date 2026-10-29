import CedarPooSpec.Cloud.Pipeline.SourceControlBoundary
import LeanPoo.Object.Definition
import CedarPooSpec.Functional.ObjectProfile

/-! A source-control prototype. A child replaces only the branch slot; the
inherited control slot reads final self and builds the corresponding policy.
This keeps branch variants in one C4 object family. -/

namespace CedarPooSpec.Cloud.Pipeline.SourceProfile

open Cedar.Spec LeanPoo

inductive Key where
  | template
  | branch
  | control
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .template => SourceControlBoundary
  | .branch => String
  | .control => SourceControlBoundary

abbrev Object := LeanPoo.Object.Memoized Key Value

def define (name : String) (boundary : SourceControlBoundary) :
    Except C4.Error Object :=
  LeanPoo.Object.define name do
    LeanPoo.Object.Declaration.Builder.value .template boundary
    LeanPoo.Object.Declaration.Builder.value .branch boundary.protectedBranch
    LeanPoo.Object.Declaration.Builder.slot .control
      (.self fun self =>
        (self .branch).map fun branch =>
          { boundary with protectedBranch := branch })

def onBranch (parent : Object) (name branch : String) :
    Except C4.Error Object :=
  parent.extendWith name do
    LeanPoo.Object.Declaration.Builder.value .branch branch

open LeanPoo.Functional.ObjectContract

def contract : Contract Object Key Unit String :=
  refine (Functional.ObjectProfile.shape [.template, .branch, .control]) fun profile path =>
    match profile.read .template, profile.read .branch, profile.read .control with
    | some template, some branch, some control =>
      if !branch.isEmpty && decide (control = { template with protectedBranch := branch }) then []
      else [.rejected path "source control projection mismatch"]
    | _, _, _ => [.rejected path "missing source control projection"]

def issues (profile : Object) := diagnose contract profile []

def control? (profile : Object) : Option SourceControlBoundary :=
  Functional.ObjectProfile.read contract profile .control

theorem control_requires_contract (profile : Object) (value : SourceControlBoundary)
    (accepted : control? profile = some value) : diagnose contract profile [] = [] :=
  Functional.ObjectProfile.read_requires_contract contract profile _ _ accepted

end CedarPooSpec.Cloud.Pipeline.SourceProfile
