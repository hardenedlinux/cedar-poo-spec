import CedarPooSpec.Authorization.Delta.Reasons

/-!
Final-reason analysis reduced to Cedar's verified authorization-equivalence
query. A policy ID belongs to the final reason set iff its analysis policyset
allows the same request. The concrete reduction is proved separately.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec Cedar.Validation CedarPooSpec.PolicyModules

private def typedPolicies (policies : Policies) (typeEnv : TypeEnv)
    (before : Bool) : Except ReasonError Policies :=
  (Cedar.SymCC.wellTypedPolicies policies typeEnv).mapError fun error =>
    .operational (.delta (if before then .beforeTypecheck error else .afterTypecheck error))

/-- An analysis-only Cedar policyset whose Allow decision represents one
    original policy ID's membership in the final determining-policy set. -/
def reasonPolicyset (policies : Policies) (id : PolicyID) : Policies :=
  match policies.find? (·.id == id) with
  | none => []
  | some policy =>
      if policy.effect == .permit then
        policies.filter (·.effect == .forbid) ++ [policy]
      else [{ policy with effect := .permit }]

private def effectiveReasonDifference? (before after : Policies)
    (id : PolicyID) (symEnv : Cedar.SymCC.SymEnv) :
    IO (Except ReasonError (Option Cedar.Spec.Env)) := do
  let left := reasonPolicyset before id
  let right := reasonPolicyset after id
  try
    let solver ← Cedar.SymCC.Solver.cvc5
    return .ok (← Cedar.SymCC.SolverM.run solver
      (Cedar.SymCC.equivalent? left right symEnv))
  catch error =>
    return .error (.solver error.toString)

structure EffectiveReasonReport where
  decision : OperationalImpactReport
  changes : List PolicyChange
  provenanceChanges : List PolicyChange
  proof : ProofFootprint
  reasonWitnesses : List ReasonWitness
  policyQueries : Nat

/-- No counterexample from Cedar's authorization-equivalence query across the
    checked schema environments. The external SMT solver remains trusted. -/
def EffectiveReasonReport.solverReasonStable (report : EffectiveReasonReport) : Bool :=
  report.reasonWitnesses.isEmpty

def EffectiveReasonReport.provenanceStable (report : EffectiveReasonReport) : Bool :=
  report.provenanceChanges.isEmpty

/-- Query final reason membership for every ID in the union of policy sets.
    A counterexample is admitted only after original Cedar replay confirms
    that the queried ID changes membership. Solver failures are errors. -/
def analyzeEffectiveReasons (revision : Revision) (schema : Schema) :
    IO (Except ReasonError EffectiveReasonReport) := do
  if !decide (revision.beforePolicies.map Policy.id).Nodup then
    return .error (.duplicatePolicyIds "before")
  if !decide (revision.afterPolicies.map Policy.id).Nodup then
    return .error (.duplicatePolicyIds "after")
  let decision ← match ← analyzeOperationalImpact revision schema with
    | .ok result => pure result
    | .error error => return .error (.operational error)
  let before := revision.beforePolicies
  let after := revision.afterPolicies
  let ids := ((before.map Policy.id) ++ (after.map Policy.id)).eraseDups
  let mut witnesses := []
  let mut policyQueries := 0
  if before != after then
    for typeEnv in schema.environments do
      let typedBefore ← match typedPolicies before typeEnv true with
        | .ok policies => pure policies
        | .error error => return .error error
      let typedAfter ← match typedPolicies after typeEnv false with
        | .ok policies => pure policies
        | .error error => return .error error
      let symEnv := Cedar.SymCC.SymEnv.ofTypeEnv typeEnv
      for id in ids do
        policyQueries := policyQueries + 1
        let possible ← match ← effectiveReasonDifference? typedBefore typedAfter id symEnv with
          | .ok possible => pure possible
          | .error error => return .error error
        if let some witness := possible then
          if !(Cedar.Validation.validateRequest schema witness.request).isOk ||
              !(Cedar.Validation.validateEntities schema witness.entities).isOk then
            return .error (.invalidWitness id)
          let beforeResponse := Cedar.Spec.isAuthorized witness.request witness.entities before
          let afterResponse := Cedar.Spec.isAuthorized witness.request witness.entities after
          let left := beforeResponse.determiningPolicies.contains id
          let right := afterResponse.determiningPolicies.contains id
          if left == right then return .error (.invalidWitness id)
          witnesses := witnesses ++
            [⟨id, typeEnv, witness, beforeResponse, afterResponse⟩]
  return .ok {
    decision
    changes := Revision.policyChanges revision
    provenanceChanges := Revision.provenanceChanges revision
    proof := Revision.proofFootprint revision
    reasonWitnesses := witnesses
    policyQueries }

structure ExplainedEffectiveReasonReport where
  beforeRoot : String
  afterRoot : String
  report : EffectiveReasonReport
  potentiallyInvalidatedRoots : List String

def analyzeModelEffectiveReasons (model : Model) (beforeRoot afterRoot : String)
    (schema : Schema) : IO (Except ReasonError ExplainedEffectiveReasonReport) := do
  let revision ← match model.compileRevision beforeRoot afterRoot with
    | .ok revision => pure revision
    | .error error => return .error (.operational (.delta (.compilation error)))
  let report ← analyzeEffectiveReasons revision schema
  return report.map fun report =>
    { beforeRoot, afterRoot, report
      potentiallyInvalidatedRoots :=
        affectedRoots model (report.changes ++ report.provenanceChanges) }

end CedarPooSpec.Authorization.Delta
