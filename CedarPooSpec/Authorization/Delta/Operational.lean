import CedarPooSpec.Authorization.Delta.Model

/-!
Qualify Cedar's decision delta for Hosts that execute only error-free Allows.
Cedar's ordinary implication query compares Allow/Deny, while the Host also
checks policy diagnostics. This module requires every policy on both sides to
be error-free throughout each schema environment before admitting that
decision delta as an error-free execution delta.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec Cedar.Validation CedarPooSpec.PolicyModules

inductive OperationalError where
  | delta (error : Error)
  | beforeError (policyId : PolicyID) (witness : Cedar.Spec.Env)
  | afterError (policyId : PolicyID) (witness : Cedar.Spec.Env)
  | invalidErrorWitness (policyId : PolicyID)
  deriving Repr

structure OperationalImpactReport where
  impact : ImpactReport
  policiesChecked : Nat
  environmentsChecked : Nat
  deriving Repr

private def checkPolicy (schema : Schema) (typeEnv : TypeEnv)
    (policy : Policy) (before : Bool) : IO (Except OperationalError Unit) := do
  let typed ← match Cedar.SymCC.wellTypedPolicy policy typeEnv with
    | .ok typed => pure typed
    | .error error =>
        return .error (.delta (if before then .beforeTypecheck error else .afterTypecheck error))
  let answer : Except OperationalError (Option Cedar.Spec.Env) ← try
    let solver ← Cedar.SymCC.Solver.cvc5
    let result ← Cedar.SymCC.SolverM.run solver
      (Cedar.SymCC.neverErrors? typed (Cedar.SymCC.SymEnv.ofTypeEnv typeEnv))
    pure (.ok result)
  catch error =>
    pure (.error (.delta (.solver error.toString)))
  match answer with
  | .error error => return .error error
  | .ok none => return .ok ()
  | .ok (some witness) =>
      if !(Cedar.Validation.validateRequest schema witness.request).isOk ||
          !(Cedar.Validation.validateEntities schema witness.entities).isOk ||
          !(Cedar.Spec.isAuthorized witness.request witness.entities
            [policy]).erroringPolicies.contains policy.id then
        return .error (.invalidErrorWitness policy.id)
      return .error (if before then .beforeError policy.id witness
        else .afterError policy.id witness)

/-- A conservative execution-delta qualification. Any possible policy error
    is returned as a witness, never silently classified as equivalence. -/
def analyzeOperationalImpact (revision : Revision) (schema : Schema) :
    IO (Except OperationalError OperationalImpactReport) := do
  if let .error error := schema.validateWellFormed then
    return .error (.delta (.schema (toString error)))
  let environments := schema.environments
  if environments.isEmpty then
    return .error (.delta .noEnvironments)
  let before := revision.beforePolicies
  let after := revision.afterPolicies
  if let .error error := Cedar.Validation.validate before schema then
    return .error (.delta (.beforeInvalid error))
  if let .error error := Cedar.Validation.validate after schema then
    return .error (.delta (.afterInvalid error))
  -- Identical policies in the same type environment have identical error
  -- behavior, so only newly introduced or edited bodies need a second query.
  let freshAfter := after.filter fun policy => !decide (policy ∈ before)
  for typeEnv in environments do
    for policy in before do
      if let .error error ← checkPolicy schema typeEnv policy true then
        return .error error
    for policy in freshAfter do
      if let .error error ← checkPolicy schema typeEnv policy false then
        return .error error
  let impact ← analyzeImpact revision schema
  return impact.mapError OperationalError.delta |>.map fun result =>
    { impact := result
      policiesChecked := (before.length + freshAfter.length) * environments.length
      environmentsChecked := environments.length }

def analyzeOperationalModelImpact (model : Model) (beforeRoot afterRoot : String)
    (schema : Schema) : IO (Except OperationalError OperationalImpactReport) := do
  match model.compileRevision beforeRoot afterRoot with
  | .error error => return .error (.delta (.compilation error))
  | .ok revision => analyzeOperationalImpact revision schema

end CedarPooSpec.Authorization.Delta
