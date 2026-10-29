import Cedar.Spec.Policy
import LeanPoo.Object.Definition
import CedarPooSpec.Functional.ObjectProfile

/-! A value-level cross-organization handoff contract. A trusted Host must
authenticate the grant and bind its claim digest to the actual data before
calling admission. This module does not issue or verify credentials. -/

namespace CedarPooSpec.Admission.Handoff

open Cedar.Spec LeanPoo

structure Scope where
  caseId : String
  claimDigest : String
  sourceActor : EntityUID
  targetActor : EntityUID
  sourceRoot : String
  targetRoot : String
  credentialMode : String
  deriving BEq, DecidableEq

structure Grant where
  scope : Scope
  epoch : Nat
  expiresAt : Nat

def Scope.wellFormed (scope : Scope) : Bool :=
  !scope.caseId.isEmpty && !scope.claimDigest.isEmpty &&
  !scope.sourceRoot.isEmpty && !scope.targetRoot.isEmpty &&
  !scope.credentialMode.isEmpty && scope.sourceActor != scope.targetActor

/-- The Host authenticates the grant; admission checks its actual current scope. -/
def Grant.admits (grant : Grant) (expected : Scope) (currentEpoch now : Nat) : Bool :=
  expected.wellFormed && grant.scope == expected && grant.epoch == currentEpoch && now < grant.expiresAt

inductive Key where
  | template
  | caseId
  | claimDigest
  | scope
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .template => Scope
  | .caseId => String
  | .claimDigest => String
  | .scope => Scope

abbrev Object := LeanPoo.Object.Memoized Key Value

def define (name : String) (initial : Scope) : Except C4.Error Object :=
  LeanPoo.Object.define name do
    LeanPoo.Object.Declaration.Builder.value .template initial
    LeanPoo.Object.Declaration.Builder.value .caseId initial.caseId
    LeanPoo.Object.Declaration.Builder.value .claimDigest initial.claimDigest
    LeanPoo.Object.Declaration.Builder.slot .scope
      (.self fun self => do
        let caseId ← self .caseId
        let claimDigest ← self .claimDigest
        pure ⟨caseId, claimDigest, initial.sourceActor, initial.targetActor,
          initial.sourceRoot, initial.targetRoot, initial.credentialMode⟩)

def onCase (parent : Object) (name caseId claimDigest : String) :
    Except C4.Error Object :=
  parent.extendWith name do
    LeanPoo.Object.Declaration.Builder.value .caseId caseId
    LeanPoo.Object.Declaration.Builder.value .claimDigest claimDigest

open LeanPoo.Functional.ObjectContract

private def shape : Contract Object Key Unit String :=
  Functional.ObjectProfile.shape [.template, .caseId, .claimDigest, .scope]
/-- Admit actual inherited projections, including exact case/digest alignment. -/
def contract : Contract Object Key Unit String :=
  refine shape fun profile path =>
    match profile.read .scope with
    | none => [.rejected path "missing handoff scope"]
    | some scope =>
      let shapeIssues := if scope.wellFormed then [] else [.rejected path "invalid handoff scope"]
      let templateAligned := match profile.read .template with
        | none => false
        | some template => decide (scope = { template with caseId := scope.caseId, claimDigest := scope.claimDigest })
      let aligned := templateAligned && profile.read .caseId == some scope.caseId &&
        profile.read .claimDigest == some scope.claimDigest
      shapeIssues ++ (if aligned then [] else [.rejected path "handoff projection mismatch"])

def issues (profile : Object) := diagnose contract profile []

def scope? (profile : Object) : Option Scope :=
  Functional.ObjectProfile.read contract profile .scope

theorem scope_requires_contract (profile : Object) (scope : Scope)
    (accepted : scope? profile = some scope) : diagnose contract profile [] = [] :=
  Functional.ObjectProfile.read_requires_contract contract profile _ _ accepted

end CedarPooSpec.Admission.Handoff
