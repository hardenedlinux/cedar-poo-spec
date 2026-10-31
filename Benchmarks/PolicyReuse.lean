import Examples.Governance.AttestedDataAccess

/-! Local timing probes for an overlay and a reorder in a 1,000-policy Cedar set. -/

namespace CedarPooSpec.PolicyReuseBenchmark

open Cedar.Spec Cedar.Validation
open CedarPooSpec.PolicyValidation
open CedarPooSpec.AttestedDataAccessExample

def policies (count : Nat) : Policies :=
  (List.range count).map fun index =>
    { projectPermit with id := s!"policy-{index}" }

def before : Policies := policies 1000
def after (token : Nat) : Policies :=
  before.dropLast ++ [{ platformVetoFreshness with id := s!"new-platform-{token}" }]

def reordered (token : Nat) : Policies :=
  let split := token % 999 + 1
  before.drop split ++ before.take split

private theorem okOfIsOk {ε : Type} (result : Except ε Unit)
    (h : result.isOk = true) : result = .ok () := by
  cases result with
  | ok value => cases value; rfl
  | error _ => cases h

theorem beforeValid : validate before schema = .ok () :=
  okOfIsOk _ (by native_decide)

def staticAfter : Policies :=
  before.dropLast ++ [platformVetoFreshness]

theorem staticFreshExact : freshPolicies before staticAfter = [platformVetoFreshness] := by
  native_decide

theorem staticReuseCount :
    staticAfter.length = 1000 ∧
    (freshPolicies before staticAfter).length = 1 := by
  native_decide

theorem staticFreshCertificates :
    ∀ policy ∈ freshPolicies before staticAfter,
      LeanPoo.Proof.Certificate (Snapshot.mk policy schema).proofObject := by
  intro policy member
  have same : policy = platformVetoFreshness := by
    simpa [staticFreshExact] using member
  subst policy
  exact (Snapshot.mk platformVetoFreshness schema).certificate
    (okOfIsOk _ (by native_decide))

/-- A concrete 1,000-policy certificate closed from 999 old bodies and one new body. -/
theorem staticAfterBundle : Bundle staticAfter schema :=
  Bundle.reviseSameSchema before staticAfter schema
    (Bundle.ofValidate before schema beforeValid)
    staticFreshCertificates

def cache : ValidatedSet schema := ⟨before, beforeValid⟩

theorem incrementalIsCedar (candidate : Policies) :
    incrementalValidate cache candidate = validate candidate schema :=
  incrementalValidate_eq_validate cache candidate

def measureFull (candidate : Policies) : IO Nat := do
  let start ← IO.monoNanosNow
  let result := validate candidate schema
  if !result.isOk then throw (IO.userError "full validation failed")
  return (← IO.monoNanosNow) - start

def measureIncremental (candidate : Policies) : IO Nat := do
  let start ← IO.monoNanosNow
  let result := incrementalValidate cache candidate
  if !result.isOk then throw (IO.userError "incremental validation failed")
  return (← IO.monoNanosNow) - start

def main : IO Unit := do
  let warmup ← IO.monoNanosNow
  discard <| measureFull (after warmup)
  discard <| measureIncremental (after warmup)
  for (scenario, makeCandidate) in
      [("overlay", after), ("reorder", reordered)] do
    for sample in [1, 2, 3] do
      let token ← IO.monoNanosNow
      let candidate := makeCandidate token
      let full ← measureFull candidate
      let incremental ← measureIncremental candidate
      IO.println s!"scenario={scenario} sample={sample} policies=1000 full_ns={full} incremental_ns={incremental}"
      IO.println s!"measurement: policy.{scenario}.full.sample{sample} {full} ns"
      IO.println s!"measurement: policy.{scenario}.incremental.sample{sample} {incremental} ns"

end CedarPooSpec.PolicyReuseBenchmark

def main : IO Unit := CedarPooSpec.PolicyReuseBenchmark.main
