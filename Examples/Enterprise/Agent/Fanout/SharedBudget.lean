import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Session.BoundedSession

/-!
Two sub-agents share one delegated external-send budget. Cedar decides each
request against facts supplied by a trusted admission host. The host must
serialize the decision and state transition across workers.
-/

namespace CedarPooSpec.SharedBudgetExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Soundness CedarPooSpec.PolicyValidation LeanPoo.Proof

def workerA : EntityUID := ⟨CedarPooSpec.BoundedSessionExample.agentType, "worker-a"⟩
def workerB : EntityUID := ⟨CedarPooSpec.BoundedSessionExample.agentType, "worker-b"⟩
def unknownWorker : EntityUID :=
  ⟨CedarPooSpec.BoundedSessionExample.agentType, "unbound-worker"⟩
def endpoint : EntityUID := CedarPooSpec.BoundedSessionExample.externalEndpoint
def sendAction : EntityUID := CedarPooSpec.BoundedSessionExample.sendAction

def contextType : RecordType := Map.make [
  ("localUsed", .required .int),
  ("localMax", .required .int),
  ("sharedUsed", .required .int),
  ("sharedMax", .required .int)]
def sendEntry : ActionSchemaEntry :=
  ⟨Set.make [CedarPooSpec.BoundedSessionExample.agentType],
    Set.make [CedarPooSpec.BoundedSessionExample.endpointType],
    Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [
      (CedarPooSpec.BoundedSessionExample.agentType,
        CedarPooSpec.BoundedSessionExample.emptyEntry),
      (CedarPooSpec.BoundedSessionExample.endpointType,
        CedarPooSpec.BoundedSessionExample.endpointEntry)],
    Map.make [(sendAction, sendEntry)]⟩
def entities : Entities := Map.make [
  (workerA, CedarPooSpec.BoundedSessionExample.emptyData),
  (workerB, CedarPooSpec.BoundedSessionExample.emptyData),
  (endpoint, CedarPooSpec.BoundedSessionExample.endpointData true),
  (sendAction, actionSchemaEntryToEntityData sendEntry)]

def fact (key : String) : Expr := .getAttr (.var .context) key
def available (used ceiling : String) : Expr :=
  .binaryApp .less (fact used) (fact ceiling)
def budgetVeto (id used ceiling : String) : Policy :=
  let body : Expr := .unaryApp .not (available used ceiling)
  { id := id, effect := .forbid,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq sendAction),
    resourceScope := .resourceScope (.eq endpoint),
    condition := [{ kind := .when, body }] }
def localVeto : Policy := budgetVeto "worker-local-budget" "localUsed" "localMax"
def sharedVeto : Policy := budgetVeto "delegation-shared-budget" "sharedUsed" "sharedMax"
def sendPermit : Policy :=
  { id := "delegated-send", effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq sendAction),
    resourceScope := .resourceScope (.eq endpoint),
    condition := [{ kind := .when, body := .lit (.bool true) }] }
/-- A permit that errors on missing facts cannot grant the action. -/
def boundedPermit : Policy :=
  let body : Expr := .and (available "localUsed" "localMax")
    (available "sharedUsed" "sharedMax")
  { sendPermit with condition := [{ kind := .when, body }] }
def incidentVeto : Policy :=
  { id := "delegation-egress-freeze", effect := .forbid,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq sendAction),
    resourceScope := .resourceScope (.eq endpoint),
    condition := [{ kind := .when, body := .lit (.bool true) }] }

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [{ name := "Base", edits := [.extend sendPermit] }] }
  let localOwner ← base.extend "Local" "Base" [.extend localVeto]
  let shared ← localOwner.extend "Shared" "Base" [.extend sharedVeto]
  let integrated ← shared.mix "Integrated" ["Local", "Shared"]
    [.overlay boundedPermit]
  let incident ← integrated.extend "Incident" "Integrated" [.extend incidentVeto]
  incident.extend "Recovered" "Incident" [.remove incidentVeto.id]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

/-- One ledger for the delegation, plus a local counter for each worker. -/

structure State where
  aUsed : Int64 := 0
  bUsed : Int64 := 0
  localMax : Int64 := 1
  sharedUsed : Int64 := 0
  sharedMax : Int64 := 1
  deriving BEq, Repr

def localUsed (state : State) (worker : EntityUID) : Int64 :=
  if worker == workerA then state.aUsed else state.bUsed
def request (state : State) (worker : EntityUID) : Request :=
  ⟨worker, sendAction, endpoint, Map.make [
    ("localUsed", .prim (.int (localUsed state worker))),
    ("localMax", .prim (.int state.localMax)),
    ("sharedUsed", .prim (.int state.sharedUsed)),
    ("sharedMax", .prim (.int state.sharedMax))]⟩
/-- Missing required facts exercise Cedar's skip-on-error rule. -/
def missingLocal : Request :=
  ⟨workerA, sendAction, endpoint, Map.make [
    ("localMax", .prim (.int 1)),
    ("sharedUsed", .prim (.int 0)),
    ("sharedMax", .prim (.int 1))]⟩
def missingShared : Request :=
  ⟨workerA, sendAction, endpoint, Map.make [
    ("localUsed", .prim (.int 0)),
    ("localMax", .prim (.int 1)),
    ("sharedMax", .prim (.int 1))]⟩
def cedarAllows
     (root : String) (req : Request)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SharedBudgetExample.model CedarPooSpec.SharedBudgetExample.schema :=
      CedarPooSpec.SharedBudgetExample.program) : Bool :=
  match programContext.response root req entities with
  | .error _ => false
  | .ok response => response.decision == .allow
def authorized
     (root : String) (state : State) (worker : EntityUID)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SharedBudgetExample.model CedarPooSpec.SharedBudgetExample.schema :=
      CedarPooSpec.SharedBudgetExample.program) : Bool :=
  if worker != workerA && worker != workerB then false
  else
    match programContext.response root (request state worker) entities with
    | .error _ => false
    | .ok response =>
        response.decision == .allow && response.erroringPolicies.isEmpty

def advance (state : State) (worker : EntityUID) : State :=
  if worker == workerA then
    { state with aUsed := state.aUsed + 1, sharedUsed := state.sharedUsed + 1 }
  else if worker == workerB then
    { state with bUsed := state.bUsed + 1, sharedUsed := state.sharedUsed + 1 }
  else state

/-- The host executes this transition atomically across all workers. -/
def admit
     (root : String) (state : State) (worker : EntityUID)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SharedBudgetExample.model CedarPooSpec.SharedBudgetExample.schema :=
      CedarPooSpec.SharedBudgetExample.program) :
    Bool × State :=
  let allowed := (authorized (programContext := programContext)) root state worker
  (allowed, if allowed then advance state worker else state)

def replay
     (root : String) (initial : State) (workers : List EntityUID)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SharedBudgetExample.model CedarPooSpec.SharedBudgetExample.schema :=
      CedarPooSpec.SharedBudgetExample.program) :
    List (Request × Bool) × State :=
  let (state, rows) := workers.foldl (fun (state, rows) worker =>
    let req := request state worker
    let (allowed, next) := (admit (programContext := programContext)) root state worker
    (next, rows ++ [(req, allowed)])) (initial, [])
  (rows, state)
def decisions
     (root : String) (initial : State) (workers : List EntityUID)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SharedBudgetExample.model CedarPooSpec.SharedBudgetExample.schema :=
      CedarPooSpec.SharedBudgetExample.program) :
    List Bool := ((replay (programContext := programContext)) root initial workers).1.map Prod.snd

def cases : List (String × String × State × List EntityUID × List Bool) := [
  ("base-allows-fanout", "Base", {}, [workerA, workerB], [true, true]),
  ("base-allows-repeat", "Base", { sharedMax := 3 },
    [workerA, workerA], [true, true]),
  ("local-budgets-still-aggregate", "Local", {}, [workerA, workerB],
    [true, true]),
  ("local-stops-worker-repeat", "Local", { sharedMax := 3 },
    [workerA, workerA], [true, false]),
  ("shared-stops-fanout", "Shared", {}, [workerA, workerB],
    [true, false]),
  ("shared-alone-allows-local-repeat", "Shared", { sharedMax := 3 },
    [workerA, workerA], [true, true]),
  ("integrated-fanout-a-first", "Integrated", {}, [workerA, workerB],
    [true, false]),
  ("integrated-fanout-b-first", "Integrated", {}, [workerB, workerA],
    [true, false]),
  ("integrated-worker-repeat", "Integrated", { sharedMax := 2 },
    [workerA, workerA, workerB], [true, false, true]),
  ("integrated-many-proposals", "Integrated", {},
    [workerA, workerB, workerA, workerB], [true, false, false, false]),
  ("shared-budget-already-spent", "Integrated", { sharedUsed := 1 },
    [workerB], [false]),
  ("incident-freezes-both", "Incident", {}, [workerA, workerB],
    [false, false]),
  ("incident-freezes-repeat", "Incident", { sharedMax := 3 },
    [workerA, workerA], [false, false]),
  ("recovered-restores-one", "Recovered", {}, [workerB, workerA],
    [true, false]),
  ("recovered-keeps-local-budget", "Recovered", { sharedMax := 3 },
    [workerA, workerA], [true, false])]

theorem casesExact :
    cases.all (fun (_, root, initial, workers, expected) =>
      decisions root initial workers == expected) = true := by native_decide

/-- Both stale checks Allow, so a host that executes both exceeds the cap. -/
theorem staleChecksAdmitBoth :
    authorized "Integrated" {} workerA = true ∧
    authorized "Integrated" {} workerB = true := by native_decide
theorem staleDoubleCommitExceedsBudget :
    (advance (advance ({} : State) workerA) workerB).sharedUsed = 2 := by
  native_decide
/-- The second decision sees the committed first action and is rejected. -/
theorem serializedAdmissionBoundsFanout :
    decisions "Integrated" {} [workerA, workerB] = [true, false] ∧
    (replay "Integrated" {} [workerA, workerB]).2.sharedUsed = 1 := by
  native_decide
theorem deniedProposalDoesNotSpendBudget :
    ((admit "Integrated" { sharedUsed := 1 } workerB).2 ==
      ({ sharedUsed := 1 } : State)) = true := by native_decide
theorem unknownWorkerDenied :
    (admit "Integrated" {} unknownWorker).1 = false ∧
    ((admit "Integrated" {} unknownWorker).2 == ({} : State)) = true := by
  native_decide
/-- Broad permit plus errored forbids can Allow; the overlay closes that hole. -/
theorem missingFactsFailClosed :
    cedarAllows "Base" missingLocal = true ∧
    cedarAllows "Integrated" missingLocal = false ∧
    cedarAllows "Integrated" missingShared = false := by native_decide

def rootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SharedBudgetExample.model CedarPooSpec.SharedBudgetExample.schema :=
      CedarPooSpec.SharedBudgetExample.program) : Bool :=
  ["Base", "Local", "Shared", "Integrated", "Incident", "Recovered"].all
    fun root => (programContext.publish root).isOk
theorem rootsValidatedExact : rootsValidated = true := by native_decide
theorem recoveredPolicies :
    (model.compile "Recovered" == model.compile "Integrated") = true := by
  native_decide

def incidentRevision : Revision :=
  (model.compileRevision "Integrated" "Incident").toOption.get (by native_decide)
theorem incidentDelta :
    incidentRevision.changedPolicyIds = [incidentVeto.id] ∧
    incidentRevision.freshPolicies = [incidentVeto] := by native_decide
def recoveryRevision : Revision :=
  (model.compileRevision "Incident" "Recovered").toOption.get (by native_decide)
theorem recoveryDelta :
    recoveryRevision.changedPolicyIds = [incidentVeto.id] ∧
    recoveryRevision.freshPolicies = [] := by native_decide

def witness : Request := request {} workerA
def baseline : AuthorizationSnapshot :=
  incidentRevision.beforeSnapshot schema witness entities
theorem baselineCertificate : Certificate baseline.proofObject :=
  baseline.certificateOfChecks (by native_decide)
private theorem okOfIsOk {ε : Type} (result : Except ε Unit)
    (accepted : result.isOk = true) : result = .ok () := by
  cases result with
  | ok value => cases value; rfl
  | error _ => cases accepted
theorem freshCertificates :
    ∀ policy ∈ incidentRevision.freshPolicies,
      Certificate (Snapshot.mk policy schema).proofObject := by
  intro policy member
  rw [incidentDelta.2] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst policy
  exact (Snapshot.mk incidentVeto schema).certificate
    (okOfIsOk _ (by native_decide))
theorem incidentCertificate :
    Certificate (incidentRevision.afterSnapshot schema witness entities).proofObject :=
  incidentRevision.authorizationCertificate schema witness entities
    (by simpa [baseline] using baselineCertificate) freshCertificates
example : Cedar.Thm.AllEvaluateToBool incidentRevision.afterPolicies witness entities :=
  certifiedAuthorizationSound
    (incidentRevision.afterSnapshot schema witness entities) incidentCertificate

end CedarPooSpec.SharedBudgetExample
