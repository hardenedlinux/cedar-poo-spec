import CedarPooSpec.Authorization.Delta.Operational
import CedarPooSpec.Authorization.Delta.Evidence

/-!
Conservative determining-policy delta over one validated schema. Cedar owns
policy matching and authorization; POO supplies revision and edit provenance.
A matching difference is only a candidate until original Cedar responses
confirm a changed determining-policy set.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec Cedar.Validation CedarPooSpec.PolicyModules

inductive ReasonError where
  | operational (error : OperationalError)
  | solver (message : String)
  | invalidWitness (policyId : PolicyID)
  | duplicatePolicyIds (side : String)
  deriving Repr

structure ReasonWitness where
  /-- The queried policy ID; several edits may contribute to this witness. -/
  policyId : PolicyID
  typeEnv : TypeEnv
  witness : Cedar.Spec.Env
  beforeResponse : Response
  afterResponse : Response
  deriving Repr

structure ReasonImpactReport where
  decision : OperationalImpactReport
  changes : List PolicyChange
  provenanceChanges : List PolicyChange
  proof : ProofFootprint
  reasonWitnesses : List ReasonWitness
  dominatedPolicyIds : List PolicyID
  unresolvedPolicyIds : List PolicyID
  matchingQueries : Nat
  dominanceQueries : Nat

def ReasonImpactReport.reasonStable (report : ReasonImpactReport) : Bool :=
  report.decision.impact.noGain && report.decision.impact.noLoss &&
    report.reasonWitnesses.isEmpty && report.unresolvedPolicyIds.isEmpty

/-- Cedar reasons and POO responsibility are separate review surfaces. -/
def ReasonImpactReport.provenanceStable (report : ReasonImpactReport) : Bool :=
  report.provenanceChanges.isEmpty

private def typed (policy : Policy) (typeEnv : TypeEnv) (before : Bool) :
    Except ReasonError Policy :=
  (Cedar.SymCC.wellTypedPolicy policy typeEnv).mapError fun error =>
    .operational (.delta (if before then .beforeTypecheck error else .afterTypecheck error))

private def matchingDifference? (before after : Option Policy) (typeEnv : TypeEnv) :
    IO (Except ReasonError (Option Cedar.Spec.Env)) := do
  let query : Except ReasonError (Cedar.SymCC.SolverM (Option Cedar.Spec.Env)) := do
    let symEnv := Cedar.SymCC.SymEnv.ofTypeEnv typeEnv
    match before, after with
    | some left, some right =>
        let left ← typed left typeEnv true
        let right ← typed right typeEnv false
        return Cedar.SymCC.matchesEquivalent? left right symEnv
    | some left, none =>
        return Cedar.SymCC.neverMatches? (← typed left typeEnv true) symEnv
    | none, some right =>
        return Cedar.SymCC.neverMatches? (← typed right typeEnv false) symEnv
    | none, none => return pure none
  let query ← match query with
    | .ok query => pure query
    | .error error => return .error error
  try
    let solver ← Cedar.SymCC.Solver.cvc5
    return .ok (← Cedar.SymCC.SolverM.run solver query)
  catch error =>
    return .error (.solver error.toString)

/-- A changed permit cannot determine the response if one unchanged forbid
    matches every input on which either version of that permit matches. Uses
    Cedar's verified policy-matching implication query. -/
private def dominatedPermit? (before after : Policies)
    (left right : Option Policy) (typeEnv : TypeEnv) :
    IO (Except ReasonError (Bool × Nat)) := do
  let variants := [(left, true), (right, false)].filterMap fun (policy, before) =>
    policy.map (·, before)
  if variants.isEmpty || variants.any (fun (policy, _) => policy.effect != .permit) then
    return .ok (false, 0)
  let commonForbids := before.filter fun policy =>
    policy.effect == .forbid && decide (policy ∈ after)
  let mut queries := 0
  for forbid in commonForbids do
    let typedForbid ← match typed forbid typeEnv true with
      | .ok policy => pure policy
      | .error error => return .error error
    let mut dominates := true
    for (permit, isBefore) in variants do
      let typedPermit ← match typed permit typeEnv isBefore with
        | .ok policy => pure policy
        | .error error => return .error error
      queries := queries + 1
      let result : Except ReasonError (Option Cedar.Spec.Env) ← try
        let solver ← Cedar.SymCC.Solver.cvc5
        pure (.ok (← Cedar.SymCC.SolverM.run solver
          (Cedar.SymCC.matchesImplies? typedPermit typedForbid
            (Cedar.SymCC.SymEnv.ofTypeEnv typeEnv))))
      catch error => pure (.error (.solver error.toString))
      match result with
      | .error error => return .error error
      | .ok (some _) =>
          dominates := false
          break
      | .ok none => pure ()
    if dominates then return .ok (true, queries)
  return .ok (false, queries)

/-- A reason-stable result requires error-free policy evaluation, equivalent
    decisions, and either unchanged matching or a verified common-forbid
    domination for every changed permit ID. Other masked candidates remain
    unresolved. -/
def analyzeReasons (revision : Revision) (schema : Schema) :
    IO (Except ReasonError ReasonImpactReport) := do
  if !decide (revision.beforePolicies.map Policy.id).Nodup then
    return .error (.duplicatePolicyIds "before")
  if !decide (revision.afterPolicies.map Policy.id).Nodup then
    return .error (.duplicatePolicyIds "after")
  let decision ← match ← analyzeOperationalImpact revision schema with
    | .ok decision => pure decision
    | .error error => return .error (.operational error)
  let before := revision.beforePolicies
  let after := revision.afterPolicies
  let mut reasonWitnesses := []
  let mut dominatedPolicyIds := []
  let mut unresolvedPolicyIds := []
  let mut matchingQueries := 0
  let mut dominanceQueries := 0
  for id in revision.changedPolicyIds do
    let left := before.find? (·.id == id)
    let right := after.find? (·.id == id)
    if left.isNone && right.isNone then
      unresolvedPolicyIds := unresolvedPolicyIds ++ [id]
      continue
    if let (some oldPolicy, some newPolicy) := (left, right) then
      if oldPolicy.effect != newPolicy.effect then
        unresolvedPolicyIds := unresolvedPolicyIds ++ [id]
        continue
    let mut found := false
    let mut masked := false
    for typeEnv in schema.environments do
      matchingQueries := matchingQueries + 1
      let possible ← match ← matchingDifference? left right typeEnv with
        | .ok possible => pure possible
        | .error error => return .error error
      if let some witness := possible then
        if !(Cedar.Validation.validateRequest schema witness.request).isOk ||
            !(Cedar.Validation.validateEntities schema witness.entities).isOk then
          return .error (.invalidWitness id)
        let beforeResponse := Cedar.Spec.isAuthorized witness.request witness.entities before
        let afterResponse := Cedar.Spec.isAuthorized witness.request witness.entities after
        if beforeResponse.determiningPolicies != afterResponse.determiningPolicies then
          reasonWitnesses := reasonWitnesses ++
            [⟨id, typeEnv, witness, beforeResponse, afterResponse⟩]
          found := true
        else
          masked := true
    if masked && !found then
      let mut dominated := decision.impact.noGain && decision.impact.noLoss
      if dominated then
        for typeEnv in schema.environments do
          let result ← match ← dominatedPermit? before after left right typeEnv with
            | .ok result => pure result
            | .error error => return .error error
          dominanceQueries := dominanceQueries + result.2
          if !result.1 then
            dominated := false
            break
      if dominated then
        dominatedPolicyIds := dominatedPolicyIds ++ [id]
      else
        unresolvedPolicyIds := unresolvedPolicyIds ++ [id]
  return .ok {
    decision
    changes := Revision.policyChanges revision
    provenanceChanges := Revision.provenanceChanges revision
    proof := Revision.proofFootprint revision
    reasonWitnesses
    dominatedPolicyIds
    unresolvedPolicyIds
    matchingQueries
    dominanceQueries }

structure ExplainedReasonImpactReport where
  beforeRoot : String
  afterRoot : String
  report : ReasonImpactReport
  potentiallyInvalidatedRoots : List String

def analyzeModelReasons (model : Model) (beforeRoot afterRoot : String)
    (schema : Schema) : IO (Except ReasonError ExplainedReasonImpactReport) := do
  let revision ← match model.compileRevision beforeRoot afterRoot with
    | .ok revision => pure revision
    | .error error => return .error (.operational (.delta (.compilation error)))
  let report ← analyzeReasons revision schema
  return report.map fun report =>
    { beforeRoot, afterRoot, report
      potentiallyInvalidatedRoots :=
        affectedRoots model (report.changes ++ report.provenanceChanges) }

end CedarPooSpec.Authorization.Delta
