import CedarPooSpec.Revision
import Cedar.SymCC
import Cedar.Validation.EnvironmentValidator

/-!
Authorization changes are analyzed using Cedar's symbolic compiler. C4 owns
the revision; Cedar owns the meaning of Allow and the symbolic query.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec Cedar.Validation CedarPooSpec.PolicyModules

inductive Error where
  | compilation (error : PolicyModules.Error)
  | schema (message : String)
  | noEnvironments
  | beforeInvalid (error : ValidationError)
  | afterInvalid (error : ValidationError)
  | beforeTypecheck (error : ValidationError)
  | afterTypecheck (error : ValidationError)
  | solver (message : String)
  | invalidWitness
  | operationChanged
  | invalidBoundedScope
  | beforeRequestInvalid
  | afterRequestInvalid
  | beforeEntitiesInvalid
  | afterEntitiesInvalid
  | policyEvaluationError
  deriving Repr

/-- A concrete request and entity store that the new revision allows and the
    old revision denies, replayed against the original Cedar policies. -/
structure Expansion where
  typeEnv : TypeEnv
  witness : Cedar.Spec.Env
  beforeResponse : Response
  afterResponse : Response
  deriving Repr

/-- A request allowed by the old revision and denied by the new one. -/
structure Contraction where
  typeEnv : TypeEnv
  witness : Cedar.Spec.Env
  beforeResponse : Response
  afterResponse : Response
  deriving Repr

/-- One query is run for every request type declared by the Cedar schema. -/
structure Report where
  changedPolicyIds : List PolicyID
  environmentsChecked : Nat
  expansions : List Expansion
  deriving Repr

def Report.noExpansion (report : Report) : Bool := report.expansions.isEmpty

/-- Both directions of a policy revision, over the same schema environments. -/
structure ImpactReport where
  changedPolicyIds : List PolicyID
  environmentsChecked : Nat
  gains : List Expansion
  losses : List Contraction
  deriving Repr

def ImpactReport.noGain (report : ImpactReport) : Bool := report.gains.isEmpty
def ImpactReport.noLoss (report : ImpactReport) : Bool := report.losses.isEmpty

/-- Classify the covered schema behavior after querying both implications.
    Solver errors never produce an ImpactReport. -/
def ImpactReport.classification (report : ImpactReport) : String :=
  if report.noGain then
    if report.noLoss then "equivalent-in-schema" else "loss-only"
  else if report.noLoss then "gain-only" else "mixed"

/-- A finite comparison of one operation under two Host-supplied snapshots.
    Unlike ImpactReport, this makes no claim about all schema requests. -/
structure SnapshotImpact where
  beforeResponse : Response
  afterResponse : Response
  deriving Repr

def SnapshotImpact.gained (report : SnapshotImpact) : Bool :=
  report.beforeResponse.decision == .deny && report.afterResponse.decision == .allow

def SnapshotImpact.lost (report : SnapshotImpact) : Bool :=
  report.beforeResponse.decision == .allow && report.afterResponse.decision == .deny

/-- Compare consent, classification, or other authenticated entity/context
    snapshots for the same principal, action, and resource. The Host owns the
    truth and freshness of both snapshots. -/
def compareOperationSnapshots (schema : Schema)
    (beforePolicies afterPolicies : Policies)
    (before after : Cedar.Spec.Env) : Except Error SnapshotImpact := do
  if before.request.principal != after.request.principal ||
      before.request.action != after.request.action ||
      before.request.resource != after.request.resource then
    throw .operationChanged
  if let .error error := schema.validateWellFormed then
    throw (.schema (toString error))
  if let .error error := Cedar.Validation.validate beforePolicies schema then
    throw (.beforeInvalid error)
  if let .error error := Cedar.Validation.validate afterPolicies schema then
    throw (.afterInvalid error)
  if let .error _ := Cedar.Validation.validateRequest schema before.request then
    throw .beforeRequestInvalid
  if let .error _ := Cedar.Validation.validateRequest schema after.request then
    throw .afterRequestInvalid
  if let .error _ := Cedar.Validation.validateEntities schema before.entities then
    throw .beforeEntitiesInvalid
  if let .error _ := Cedar.Validation.validateEntities schema after.entities then
    throw .afterEntitiesInvalid
  let beforeResponse := Cedar.Spec.isAuthorized before.request before.entities beforePolicies
  let afterResponse := Cedar.Spec.isAuthorized after.request after.entities afterPolicies
  if !beforeResponse.erroringPolicies.isEmpty || !afterResponse.erroringPolicies.isEmpty then
    throw .policyEvaluationError
  return { beforeResponse, afterResponse }

/-- Check `Allow(new) → Allow(old)` in each schema environment. A solver error,
    unknown result, or failed witness replay never becomes a no-expansion result.
    The symbolic implication and its proof are owned by upstream Cedar. -/
def analyze (revision : Revision) (schema : Schema) : IO (Except Error Report) := do
  if let .error error := schema.validateWellFormed then
    return .error (.schema (toString error))
  let environments := schema.environments
  if environments.isEmpty then
    return .error .noEnvironments
  let before := revision.beforePolicies
  let after := revision.afterPolicies
  if let .error error := Cedar.Validation.validate before schema then
    return .error (.beforeInvalid error)
  if let .error error := Cedar.Validation.validate after schema then
    return .error (.afterInvalid error)
  let mut expansions : List Expansion := []
  for typeEnv in environments do
    let typedBefore ← match Cedar.SymCC.wellTypedPolicies before typeEnv with
      | .ok policies => pure policies
      | .error error => return .error (.beforeTypecheck error)
    let typedAfter ← match Cedar.SymCC.wellTypedPolicies after typeEnv with
      | .ok policies => pure policies
      | .error error => return .error (.afterTypecheck error)
    let answer : Except Error (Option Cedar.Spec.Env) ← try
      let solver ← Cedar.SymCC.Solver.cvc5
      let result ← Cedar.SymCC.SolverM.run solver
        (Cedar.SymCC.implies? typedAfter typedBefore
          (Cedar.SymCC.SymEnv.ofTypeEnv typeEnv))
      pure (.ok result)
    catch error =>
      pure (.error (.solver error.toString))
    match answer with
    | .error error => return .error error
    | .ok none => pure ()
    | .ok (some witness) =>
      if let .error _ := Cedar.Validation.validateRequest schema witness.request then
        return .error .invalidWitness
      if let .error _ := Cedar.Validation.validateEntities schema witness.entities then
        return .error .invalidWitness
      let beforeResponse := Cedar.Spec.isAuthorized witness.request witness.entities before
      let afterResponse := Cedar.Spec.isAuthorized witness.request witness.entities after
      if beforeResponse.decision != .deny || afterResponse.decision != .allow then
        return .error .invalidWitness
      expansions := expansions ++ [⟨typeEnv, witness, beforeResponse, afterResponse⟩]
  return .ok {
    changedPolicyIds := revision.changedPolicyIds
    environmentsChecked := environments.length
    expansions
  }

/-- Compile both POO roots before asking Cedar for their authorization delta. -/
def analyzeModel (model : Model) (beforeRoot afterRoot : String) (schema : Schema) :
    IO (Except Error Report) := do
  match model.compileRevision beforeRoot afterRoot with
  | .error error => return .error (.compilation error)
  | .ok revision => analyze revision schema

/-- Analyze grants and revocations. The reverse query finds losses, then swaps
    each replay response back into the original before/after orientation. -/
def analyzeImpact (revision : Revision) (schema : Schema) :
    IO (Except Error ImpactReport) := do
  let gains ← analyze revision schema
  let losses ← analyze { before := revision.after, after := revision.before } schema
  return do
    let gained ← gains
    let lost ← losses
    return {
      changedPolicyIds := gained.changedPolicyIds
      environmentsChecked := gained.environmentsChecked
      gains := gained.expansions
      losses := lost.expansions.map fun item =>
        { typeEnv := item.typeEnv, witness := item.witness,
          beforeResponse := item.afterResponse,
          afterResponse := item.beforeResponse }
    }

def analyzeModelImpact (model : Model) (beforeRoot afterRoot : String)
    (schema : Schema) : IO (Except Error ImpactReport) := do
  match model.compileRevision beforeRoot afterRoot with
  | .error error => return .error (.compilation error)
  | .ok revision => analyzeImpact revision schema

end CedarPooSpec.Authorization.Delta
