import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Revision
import CedarPooSpec.PolicyJson
import CedarPooSpec.Authorization.Compound
import Cedar.Validation.RequestEntityValidator

/-!
Tsai and Hariri (2026) study high-level driving commands that remain locally
safe but make a mission infeasible. This example projects a finite successor
summary into Cedar authorization. The paper uses fault injection, not a VLA
prompt-injection experiment; the VLA connection is a proposed application.
-/

namespace CedarPooSpec.SuccessorBoundaryExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Soundness CedarPooSpec.PolicyValidation LeanPoo.Proof

def plannerType : EntityType := ⟨"MissionPlanner", []⟩
def routeType : EntityType := ⟨"RouteCandidate", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def planner : EntityUID := ⟨plannerType, "untrusted-planner"⟩
def route : EntityUID := ⟨routeType, "proposed-route"⟩
def proceed : EntityUID := ⟨actionType, "proceed"⟩
def fallback : EntityUID := ⟨actionType, "fallback-handoff"⟩

def emptyEntry : EntitySchemaEntry := .standard ⟨Set.empty, Map.empty, none⟩
def contextType : RecordType := Map.make [
  ("routeApproved", .required (.bool .anyBool)),
  ("successorPlatformSafe", .required (.bool .anyBool)),
  ("successorMissionFeasible", .required (.bool .anyBool)),
  ("proposalId", .required .int),
  ("witnessProposalId", .required .int),
  ("missionVersion", .required .int),
  ("witnessMissionVersion", .required .int),
  ("vehicleStateId", .required .int),
  ("witnessVehicleStateId", .required .int),
  ("decisionTick", .required .int),
  ("observedTick", .required .int)]
def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [plannerType], Set.make [routeType], Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [(plannerType, emptyEntry), (routeType, emptyEntry)],
    Map.make [(proceed, actionEntry), (fallback, actionEntry)]⟩
def emptyData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }
def entities : Entities := Map.make [
  (planner, emptyData), (route, emptyData),
  (proceed, actionSchemaEntryToEntityData actionEntry),
  (fallback, actionSchemaEntryToEntityData actionEntry)]

/- Each element is one predicted successor, not a sensor measurement. -/
structure Successor where
  collisionClear : Bool := true
  roadClear : Bool := true
  checkpointReachable : Bool := true
  restrictedClear : Bool := true
  budgetEnough : Bool := true
  deriving DecidableEq, Repr

def platformSafe (steps : List Successor) : Bool :=
  !steps.isEmpty && steps.all (fun step => step.collisionClear && step.roadClear)
def missionFeasible (steps : List Successor) : Bool :=
  !steps.isEmpty && steps.all (fun step =>
    step.checkpointReachable && step.restrictedClear && step.budgetEnough)

/- The host authenticates this witness before the adapter receives it. -/
structure HorizonWitness where
  proposalId : Int64 := 7
  missionVersion : Int64 := 4
  vehicleStateId : Int64 := 12
  observedTick : Int64 := 9
  steps : List Successor := [{}, {}]

structure Candidate where
  proposalId : Int64 := 7
  missionVersion : Int64 := 4
  vehicleStateId : Int64 := 12
  decisionTick : Int64 := 10
  routeApproved : Bool := true
  witness : HorizonWitness := {}

def request (action : EntityUID) (candidate : Candidate) : Request :=
  ⟨planner, action, route, Map.make [
    ("routeApproved", .prim (.bool candidate.routeApproved)),
    ("successorPlatformSafe", .prim (.bool (platformSafe candidate.witness.steps))),
    ("successorMissionFeasible", .prim (.bool (missionFeasible candidate.witness.steps))),
    ("proposalId", .prim (.int candidate.proposalId)),
    ("witnessProposalId", .prim (.int candidate.witness.proposalId)),
    ("missionVersion", .prim (.int candidate.missionVersion)),
    ("witnessMissionVersion", .prim (.int candidate.witness.missionVersion)),
    ("vehicleStateId", .prim (.int candidate.vehicleStateId)),
    ("witnessVehicleStateId", .prim (.int candidate.witness.vehicleStateId)),
    ("decisionTick", .prim (.int candidate.decisionTick)),
    ("observedTick", .prim (.int candidate.witness.observedTick))]⟩

def ctx (name : String) : Expr := .getAttr (.var .context) name
def neg (body : Expr) : Expr := .unaryApp .not body
def eqCtx (left right : String) : Expr :=
  .binaryApp .eq (ctx left) (ctx right)
def witnessBinding : Expr :=
  .and (eqCtx "proposalId" "witnessProposalId")
    (.and (eqCtx "missionVersion" "witnessMissionVersion")
      (eqCtx "vehicleStateId" "witnessVehicleStateId"))
def horizonFresh : Expr :=
  .and (.binaryApp .lessEq (.lit (.int 0)) (ctx "observedTick"))
    (.and (.binaryApp .lessEq (ctx "observedTick") (ctx "decisionTick"))
      (.binaryApp .lessEq
        (.binaryApp .sub (ctx "decisionTick") (ctx "observedTick"))
        (.lit (.int 2))))
def policy (id : String) (effect : Effect) (action : EntityUID)
    (body : Expr) : Policy :=
  { id, effect,
    principalScope := .principalScope (.eq planner),
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body }] }

def nominal : Policy :=
  policy "nominal-route" .permit proceed (ctx "routeApproved")
def safeFallback : Policy :=
  policy "fallback-handoff" .permit fallback (.lit (.bool true))
def platformCondition : Expr :=
  .and (ctx "routeApproved") (ctx "successorPlatformSafe")
def platformChecked : Policy :=
  { nominal with condition := [
      { kind := .when,
        body := platformCondition }] }
def missionVeto : Policy :=
  policy "mission-infeasible" .forbid proceed
    (neg (ctx "successorMissionFeasible"))
def evidenceVeto : Policy :=
  policy "unbound-successor-witness" .forbid proceed
    (neg witnessBinding)
def currentNominal : Policy :=
  { platformChecked with condition := [
      { kind := .when,
        body := .and platformCondition
          (.and (ctx "successorMissionFeasible")
            (.and witnessBinding horizonFresh)) }] }

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [.extend nominal, .extend safeFallback] }] }
  let platform ← base.extend "Platform" "Base" [.overlay platformChecked]
  let mission ← platform.extend "Mission" "Base" [.extend missionVeto]
  let evidence ← mission.extend "Evidence" "Base" [.extend evidenceVeto]
  let integrated ← evidence.mix "Integrated" ["Platform", "Mission", "Evidence"]
  integrated.extend "Current" "Integrated" [.overlay currentNominal]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

def authorizedRequest
     (root : String) (req : Request)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SuccessorBoundaryExample.model CedarPooSpec.SuccessorBoundaryExample.schema :=
      CedarPooSpec.SuccessorBoundaryExample.program) : Bool :=
  match programContext.authorizeLayers [(root, req)] entities with
  | .error _ => false
  | .ok receipts => CedarPooSpec.Authorization.Compound.layersAllowed receipts
def authorized
     (root : String) (action : EntityUID) (candidate : Candidate)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SuccessorBoundaryExample.model CedarPooSpec.SuccessorBoundaryExample.schema :=
      CedarPooSpec.SuccessorBoundaryExample.program) : Bool :=
  (authorizedRequest (programContext := programContext)) root (request action candidate)

def clear : Candidate := {}
def withSteps (steps : List Successor) : Candidate :=
  { witness := { steps := steps } }
def collision : Candidate := withSteps [{}, { collisionClear := false }]
def roadExit : Candidate := withSteps [{}, { roadClear := false }]
def skippedCheckpoint : Candidate :=
  withSteps [{}, { checkpointReachable := false }]
def restrictedRegion : Candidate :=
  withSteps [{}, { restrictedClear := false }]
def depletedBudget : Candidate := withSteps [{}, { budgetEnough := false }]
def unbound : Candidate :=
  { clear with witness := { clear.witness with proposalId := 8 } }
def wrongMission : Candidate :=
  { clear with missionVersion := 5 }
def wrongVehicleState : Candidate :=
  { clear with vehicleStateId := 13 }
def stale : Candidate :=
  { clear with witness := { clear.witness with observedTick := 7 } }
def futureDated : Candidate :=
  { clear with witness := { clear.witness with observedTick := 11 } }
def negativeObservation : Candidate :=
  { clear with witness := { clear.witness with observedTick := -1 } }
def nearTickLimit : Candidate :=
  { decisionTick := 9223372036854775807,
    witness := { observedTick := 9223372036854775806 } }
def emptyHorizon : Candidate := withSteps []

def cases : List (String × String × EntityUID × Candidate × Bool) := [
  ("base-misses-future-collision", "Base", proceed, collision, true),
  ("platform-blocks-future-collision", "Platform", proceed, collision, false),
  ("platform-misses-checkpoint", "Platform", proceed, skippedCheckpoint, true),
  ("mission-blocks-checkpoint", "Mission", proceed, skippedCheckpoint, false),
  ("mission-misses-future-collision", "Mission", proceed, collision, true),
  ("evidence-blocks-unbound-witness", "Evidence", proceed, unbound, false),
  ("integrated-allows-admissible", "Integrated", proceed, clear, true),
  ("integrated-blocks-collision", "Integrated", proceed, collision, false),
  ("integrated-blocks-road-exit", "Integrated", proceed, roadExit, false),
  ("integrated-blocks-skipped-checkpoint", "Integrated", proceed, skippedCheckpoint, false),
  ("integrated-blocks-restricted-region", "Integrated", proceed, restrictedRegion, false),
  ("integrated-blocks-budget-exhaustion", "Integrated", proceed, depletedBudget, false),
  ("integrated-rejects-empty-horizon", "Integrated", proceed, emptyHorizon, false),
  ("integrated-blocks-unbound-witness", "Integrated", proceed, unbound, false),
  ("integrated-allows-stale-horizon", "Integrated", proceed, stale, true),
  ("current-blocks-stale-horizon", "Current", proceed, stale, false),
  ("current-blocks-other-proposal-witness", "Current", proceed, unbound, false),
  ("current-blocks-other-mission-version", "Current", proceed, wrongMission, false),
  ("current-blocks-other-vehicle-state", "Current", proceed, wrongVehicleState, false),
  ("current-blocks-future-dated-witness", "Current", proceed, futureDated, false),
  ("current-blocks-negative-observation", "Current", proceed, negativeObservation, false),
  ("current-allows-near-int64-limit", "Current", proceed, nearTickLimit, true),
  ("current-allows-fresh-horizon", "Current", proceed, clear, true),
  ("current-keeps-fallback-available", "Current", fallback, collision, true)]

def casesExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SuccessorBoundaryExample.model CedarPooSpec.SuccessorBoundaryExample.schema :=
      CedarPooSpec.SuccessorBoundaryExample.program) : Bool := cases.all fun (_, root, action, candidate, expected) =>
  (authorized (programContext := programContext)) root action candidate == expected
theorem casesExactFully : casesExact = true := by native_decide
theorem sameProposalDifferentSuccessor :
    clear.proposalId = skippedCheckpoint.proposalId ∧
    authorized "Current" proceed clear = true ∧
    authorized "Current" proceed skippedCheckpoint = false := by native_decide

/- The actual successor is deliberately outside the Cedar request. This
   exhibits the limit of authorization when a predictor is wrong or stale. -/
structure Execution where
  proposal : Candidate
  actualSuccessors : List Successor

def expectedExecution : Execution :=
  { proposal := clear, actualSuccessors := clear.witness.steps }
def redirectedExecution : Execution :=
  { proposal := clear, actualSuccessors := skippedCheckpoint.witness.steps }

theorem unobservedTrajectoryCounterexample :
    request proceed expectedExecution.proposal =
      request proceed redirectedExecution.proposal ∧
    missionFeasible expectedExecution.actualSuccessors = true ∧
    missionFeasible redirectedExecution.actualSuccessors = false ∧
    authorized "Current" proceed redirectedExecution.proposal = true := by
  native_decide

def withoutContextField (field : String) : Request :=
  let original := request proceed clear
  let reduced := Map.filter (fun name _ => name != field) original.context
  { original with context := reduced }
def missingMissionSummary : Request := withoutContextField "successorMissionFeasible"
def missingWitnessId : Request := withoutContextField "witnessProposalId"
theorem missingEvidenceDenied :
    authorizedRequest "Current" missingMissionSummary = false ∧
    authorizedRequest "Current" missingWitnessId = false := by native_decide

def matrixColumns : List (String × Candidate) := [
  ("collision", collision), ("checkpoint", skippedCheckpoint),
  ("restricted", restrictedRegion), ("budget", depletedBudget),
  ("clear", clear), ("unbound", unbound), ("stale", stale)]
def matrixExpectations : List (String × List Bool) := [
  ("Base",       [true,  true,  true,  true,  true, true,  true]),
  ("Platform",   [false, true,  true,  true,  true, true,  true]),
  ("Mission",    [true,  false, false, false, true, true,  true]),
  ("Evidence",   [true,  true,  true,  true,  true, false, true]),
  ("Integrated", [false, false, false, false, true, false, true]),
  ("Current",    [false, false, false, false, true, false, false])]
def matrixCases : List (String × String × EntityUID × Candidate × Bool) :=
  matrixExpectations.flatMap fun (root, expected) =>
    (matrixColumns.zip expected).map fun ((label, candidate), allow) =>
      (s!"matrix-{root.toLower}-{label}", root, proceed, candidate, allow)
theorem matrixComplete : matrixCases.length = 42 := by native_decide
theorem matrixExact :
    matrixCases.all (fun (_, root, action, candidate, expected) =>
      authorized root action candidate == expected) = true := by native_decide

def rootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SuccessorBoundaryExample.model CedarPooSpec.SuccessorBoundaryExample.schema :=
      CedarPooSpec.SuccessorBoundaryExample.program) : Bool :=
  ["Base", "Platform", "Mission", "Evidence", "Integrated", "Current"].all fun root =>
    (programContext.publish root).isOk
theorem rootsValidatedFully : rootsValidated = true := by native_decide

def freshnessRevision : Revision :=
  (model.compileRevision "Integrated" "Current").toOption.get (by native_decide)
theorem freshnessDelta :
    freshnessRevision.changedPolicyIds = [nominal.id] ∧
    freshnessRevision.freshPolicies = [currentNominal] := by native_decide

def witness : Request := request proceed stale
def before : AuthorizationSnapshot :=
  freshnessRevision.beforeSnapshot schema witness entities
theorem baselineCertificate : Certificate before.proofObject :=
  before.certificateOfChecks (by native_decide)
private theorem okOfIsOk {ε : Type} (result : Except ε Unit)
    (accepted : result.isOk = true) : result = .ok () := by
  cases result with
  | ok value => cases value; rfl
  | error _ => cases accepted
theorem freshCertificates :
    ∀ p ∈ freshnessRevision.freshPolicies,
      Certificate (Snapshot.mk p schema).proofObject := by
  intro p member
  rw [freshnessDelta.2] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst p
  exact (Snapshot.mk currentNominal schema).certificate
    (okOfIsOk _ (by native_decide))
theorem currentCertificate :
    Certificate (freshnessRevision.afterSnapshot schema witness entities).proofObject :=
  freshnessRevision.authorizationCertificate schema witness entities
    (by simpa [before] using baselineCertificate) freshCertificates
example : Cedar.Thm.AllEvaluateToBool freshnessRevision.afterPolicies witness entities :=
  certifiedAuthorizationSound
    (freshnessRevision.afterSnapshot schema witness entities) currentCertificate

end CedarPooSpec.SuccessorBoundaryExample
