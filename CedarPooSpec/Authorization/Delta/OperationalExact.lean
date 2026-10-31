import CedarPooSpec.Authorization.Delta.Operational

/-!
An exact symbolic query for a Host that executes only error-free Allows. The
query combines Cedar's symbolic authorizer with Cedar's symbolic evaluation of
each policy body. The concrete witness is checked against Cedar.Spec.Response.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec Cedar.Validation CedarPooSpec.PolicyModules
open Cedar.SymCC.Factory

/-- The Host's executable authorization predicate, using Cedar's own response
    and diagnostic set. -/
def errorFreeAllow (policies : Policies) (env : Cedar.Spec.Env) : Bool :=
  let response := Cedar.Spec.isAuthorized env.request env.entities policies
  response.decision == .allow && response.erroringPolicies.isEmpty

/-- Every policy evaluation returns a value rather than an error. -/
def allEvaluated : List Cedar.SymCC.Term → Cedar.SymCC.Term
  | [] => true
  | term :: rest => Cedar.SymCC.Factory.and
      (Cedar.SymCC.Factory.isSome term) (allEvaluated rest)

/-- Cedar's Allow decision conjoined with successful evaluation of every
    policy, matching the Host's error-free execution rule. -/
def symbolicErrorFreeAllow (decision : Cedar.SymCC.Term)
    (policyResults : List Cedar.SymCC.Term) : Cedar.SymCC.Term :=
  Cedar.SymCC.Factory.and decision (allEvaluated policyResults)

/-- Asserts are satisfiable exactly when the after revision has an error-free
    Allow and the before revision does not. Both authorization decisions and
    all policy evaluations use Cedar's symbolic compiler. -/
def verifyErrorFreeAllowExpansion (before after : Policies)
    (εnv : Cedar.SymCC.SymEnv) : Cedar.SymCC.Result Cedar.SymCC.Asserts := do
  let beforeDecision ← Cedar.SymCC.isAuthorized before εnv
  let afterDecision ← Cedar.SymCC.isAuthorized after εnv
  let beforeResults ← before.mapM fun policy =>
    Cedar.SymCC.compile policy.toExpr εnv
  let afterResults ← after.mapM fun policy =>
    Cedar.SymCC.compile policy.toExpr εnv
  let beforeExecutable := symbolicErrorFreeAllow beforeDecision beforeResults
  let afterExecutable := symbolicErrorFreeAllow afterDecision afterResults
  let exprs := (before ++ after).map Policy.toExpr
  return (Cedar.SymCC.enforce exprs εnv).elts ++
    [Cedar.SymCC.Factory.and afterExecutable
      (Cedar.SymCC.Factory.not beforeExecutable)]

structure ExactExecutionWitness where
  typeEnv : TypeEnv
  witness : Cedar.Spec.Env
  beforeResponse : Response
  afterResponse : Response
  deriving Repr

structure ExactOperationalImpactReport where
  changedPolicyIds : List PolicyID
  environmentsChecked : Nat
  gains : List ExactExecutionWitness
  losses : List ExactExecutionWitness
  deriving Repr

def ExactOperationalImpactReport.classification
    (report : ExactOperationalImpactReport) : String :=
  if report.gains.isEmpty then
    if report.losses.isEmpty then "equivalent-in-schema" else "loss-only"
  else if report.losses.isEmpty then "gain-only" else "mixed"

inductive ExactOperationalError where
  | delta (error : Error)
  | invalidWitness
  deriving Repr

private def findExactGains (before after : Policies) (schema : Schema) :
    IO (Except ExactOperationalError (List ExactExecutionWitness)) := do
  let mut gains := []
  for typeEnv in schema.environments do
    let typedBefore ← match Cedar.SymCC.wellTypedPolicies before typeEnv with
      | .ok policies => pure policies
      | .error error => return .error (.delta (.beforeTypecheck error))
    let typedAfter ← match Cedar.SymCC.wellTypedPolicies after typeEnv with
      | .ok policies => pure policies
      | .error error => return .error (.delta (.afterTypecheck error))
    let answer : Except ExactOperationalError (Option Cedar.Spec.Env) ← try
      let solver ← Cedar.SymCC.Solver.cvc5
      let result ← Cedar.SymCC.SolverM.run solver
        (Cedar.SymCC.sat? (typedBefore ++ typedAfter)
          (verifyErrorFreeAllowExpansion typedBefore typedAfter)
          (Cedar.SymCC.SymEnv.ofTypeEnv typeEnv))
      pure (.ok result)
    catch error =>
      pure (.error (.delta (.solver error.toString)))
    match answer with
    | .error error => return .error error
    | .ok none => pure ()
    | .ok (some witness) =>
      if !(Cedar.Validation.validateRequest schema witness.request).isOk ||
          !(Cedar.Validation.validateEntities schema witness.entities).isOk ||
          errorFreeAllow after witness != true ||
          errorFreeAllow before witness != false then
        return .error .invalidWitness
      gains := gains ++ [⟨typeEnv, witness,
        Cedar.Spec.isAuthorized witness.request witness.entities before,
        Cedar.Spec.isAuthorized witness.request witness.entities after⟩]
  return .ok gains

/-- Query both directions of the exact executable predicate. A satisfiable
    witness is validated and replayed with the original, untransformed Cedar
    policies. Unknown solver results and invalid witnesses fail closed. -/
def analyzeExactOperationalImpact (revision : Revision) (schema : Schema) :
    IO (Except ExactOperationalError ExactOperationalImpactReport) := do
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
  let gains ← match ← findExactGains before after schema with
    | .ok result => pure result
    | .error error => return .error error
  let reversed ← match ← findExactGains after before schema with
    | .ok result => pure result
    | .error error => return .error error
  return .ok ⟨revision.changedPolicyIds, environments.length, gains,
    reversed.map fun item =>
      ⟨item.typeEnv, item.witness, item.afterResponse,
        item.beforeResponse⟩⟩

def analyzeExactOperationalModelImpact (model : Model)
    (beforeRoot afterRoot : String) (schema : Schema) :
    IO (Except ExactOperationalError ExactOperationalImpactReport) := do
  match model.compileRevision beforeRoot afterRoot with
  | .error error => return .error (.delta (.compilation error))
  | .ok revision => analyzeExactOperationalImpact revision schema

end CedarPooSpec.Authorization.Delta
