import CedarPooSpec.Admission.OperationIdentity

/-! Platform-neutral Gateway bindings. Identities must denote authenticated
canonical Host artifacts; their equality does not authenticate those artifacts. -/
namespace CedarPooSpec.Gateway

structure Scope where
  originalRoot : String
  claim : String
  canonicalOperation : String
  profile : String
  budgetDomain : String
  historyDomain : String
  schemaIdentity : String
  sourceCut : String
  moduleClosure : String
  projectionClosure : String
  deriving DecidableEq, Repr

def Scope.valid (scope : Scope) : Bool :=
  [scope.originalRoot, scope.claim, scope.canonicalOperation, scope.profile, scope.budgetDomain,
   scope.historyDomain, scope.schemaIdentity, scope.sourceCut,
   scope.moduleClosure, scope.projectionClosure].all (!·.isEmpty)

structure Context where
  scope : Scope
  policyRevision : Nat
  ownerEpoch : Nat
  historyRevision : Nat
  factFloor : Nat
  deriving DecidableEq, Repr

inductive EvidenceStatus where
  | satisfied | refused | unknown
  deriving DecidableEq, Repr

structure Assessment where
  name : String
  status : EvidenceStatus
  deriving DecidableEq, Repr

/-- An admitted Profile fixes required checks, not an agent-selected list. -/
structure Profile where
  identity : String
  requiredChecks : List String
  deriving DecidableEq, Repr

def Profile.valid (profile : Profile) : Bool :=
  !profile.identity.isEmpty && !profile.requiredChecks.isEmpty &&
  profile.requiredChecks.all (!·.isEmpty) &&
  decide profile.requiredChecks.Nodup

/-- Every original required check must be present exactly once and satisfied.
The declared order remains part of the Profile's deterministic contract. -/
def Profile.accepts (profile : Profile) (checks : List Assessment) : Bool :=
  checks.all (fun check => decide (check.status = .satisfied)) &&
  (profile.valid && decide (checks.map (·.name) = profile.requiredChecks))

theorem accepted_assessments_are_satisfied (profile : Profile) (checks : List Assessment)
    (accepted : profile.accepts checks = true) :
    ∀ check ∈ checks, check.status = .satisfied := by
  have h := (Bool.and_eq_true_iff.mp accepted).1
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem unknown_assessment_cannot_be_accepted (profile : Profile) (checks : List Assessment)
    (check : Assessment) (member : check ∈ checks) (unknown : check.status = .unknown) :
    profile.accepts checks = false := by
  cases h : profile.accepts checks with
  | false => rfl
  | true =>
    have known := accepted_assessments_are_satisfied profile checks h check member
    simp [unknown] at known

end CedarPooSpec.Gateway
