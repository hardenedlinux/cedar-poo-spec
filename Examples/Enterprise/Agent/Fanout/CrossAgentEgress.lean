import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Functional.Admission
import Examples.Enterprise.Agent.Fanout.SharedBudget
import CedarPooSpec.SchemaJson
import CedarPooSpec.Admission.PolicySnapshot
import CedarPooSpec.Admission.AuthorityConsumption
import CedarPooSpec.Admission.OperationIdentity

/-!
One worker reads a sensitive document and another proposes external egress.
The policy owners reuse the bounded-session history and intent controls and
the fanout budget controls. The admission host owns the shared lineage ledger.
-/

namespace CedarPooSpec.CrossAgentEgressExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules

def workerA : EntityUID := CedarPooSpec.SharedBudgetExample.workerA
def workerB : EntityUID := CedarPooSpec.SharedBudgetExample.workerB
def secretDoc : EntityUID := CedarPooSpec.BoundedSessionExample.secretDoc
def publicDoc : EntityUID := CedarPooSpec.BoundedSessionExample.publicDoc
def externalEndpoint : EntityUID := CedarPooSpec.SharedBudgetExample.endpoint
def readAction : EntityUID := CedarPooSpec.BoundedSessionExample.readAction
def sendAction : EntityUID := CedarPooSpec.SharedBudgetExample.sendAction

def contextType : RecordType := Map.make [
  ("localUsed", .required .int), ("localMax", .required .int),
  ("sharedUsed", .required .int), ("sharedMax", .required .int),
  ("sensitiveSeen", .required (.bool .anyBool)),
  ("intent", .required .string), ("delegatedIntent", .required .string)]
def readEntry : ActionSchemaEntry :=
  ⟨Set.make [CedarPooSpec.BoundedSessionExample.agentType],
    Set.make [CedarPooSpec.BoundedSessionExample.documentType],
    Set.empty, contextType⟩
def sendEntry : ActionSchemaEntry :=
  ⟨Set.make [CedarPooSpec.BoundedSessionExample.agentType],
    Set.make [CedarPooSpec.BoundedSessionExample.endpointType],
    Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [
      (CedarPooSpec.BoundedSessionExample.agentType,
        CedarPooSpec.BoundedSessionExample.emptyEntry),
      (CedarPooSpec.BoundedSessionExample.documentType,
        CedarPooSpec.BoundedSessionExample.documentEntry),
      (CedarPooSpec.BoundedSessionExample.endpointType,
        CedarPooSpec.BoundedSessionExample.endpointEntry)],
    Map.make [(readAction, readEntry), (sendAction, sendEntry)]⟩
def entities : Entities := Map.make [
  (workerA, CedarPooSpec.BoundedSessionExample.emptyData),
  (workerB, CedarPooSpec.BoundedSessionExample.emptyData),
  (secretDoc, CedarPooSpec.BoundedSessionExample.documentData true),
  (publicDoc, CedarPooSpec.BoundedSessionExample.documentData false),
  (externalEndpoint, CedarPooSpec.BoundedSessionExample.endpointData true),
  (readAction, actionSchemaEntryToEntityData readEntry),
  (sendAction, actionSchemaEntryToEntityData sendEntry)]

/-- Reuse the session policy bodies while widening the principal to the
    workers bound by the admission host. -/
def workerRead : Policy :=
  { CedarPooSpec.BoundedSessionExample.readPermit with
    principalScope := .principalScope .any }
def lineageHistory : Policy :=
  { CedarPooSpec.BoundedSessionExample.historyVeto with
    principalScope := .principalScope .any }
def delegatedIntent : Policy :=
  { CedarPooSpec.BoundedSessionExample.intentVeto with
    principalScope := .principalScope .any }

/-- Actual LeanPOO construction: inherited fanout budgets, then independently
    editable read, history, and intent owners, followed by a C4 mix. -/
def modelResult : Except LeanPoo.C4.Error Model := do
  let budget := CedarPooSpec.SharedBudgetExample.model
  let read ← budget.extend "Read" "Integrated" [.extend workerRead]
  let history ← read.extend "History" "Read" [.extend lineageHistory]
  let intent ← history.extend "Intent" "Read" [.extend delegatedIntent]
  let governed ← intent.mix "CrossAgentGoverned" ["History", "Intent"]
  let incident ← governed.extend "CrossAgentIncident" "CrossAgentGoverned"
    [.extend CedarPooSpec.SharedBudgetExample.incidentVeto]
  incident.extend "CrossAgentRecovered" "CrossAgentIncident"
    [.remove CedarPooSpec.SharedBudgetExample.incidentVeto.id]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Retain checked policies for this exact model/schema, never request decisions. -/
def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard model schema
    (model.modules.map (·.name)) (by native_decide)

inductive LedgerView where
  | workerLocal
  | delegationShared
  deriving BEq, Repr

structure Attempt where
  worker : EntityUID
  action : EntityUID
  resource : EntityUID
  intent : String := "report"
  deriving BEq, Repr

/-- The Host binds a checked request to the exact proposed tool effect. -/
structure BoundEffect where
  operationId : CedarPooSpec.Admission.OperationId
  attempt : Attempt
  payloadDigest : String
  deriving BEq, Repr

structure State where
  budget : CedarPooSpec.SharedBudgetExample.State := {}
  authority : CedarPooSpec.Admission.AuthorityLedger BoundEffect := {}
  operations : CedarPooSpec.Admission.OperationLedger := {}
  aSeen : Bool := false
  bSeen : Bool := false
  sharedSeen : Bool := false
  delegated : String := "report"
  epoch : Nat := 0
  deriving BEq, Repr

def readSecretA : Attempt := ⟨workerA, readAction, secretDoc, "report"⟩
def readPublicA : Attempt := ⟨workerA, readAction, publicDoc, "report"⟩
def sendA (intent := "report") : Attempt :=
  ⟨workerA, sendAction, externalEndpoint, intent⟩
def sendB (intent := "report") : Attempt :=
  ⟨workerB, sendAction, externalEndpoint, intent⟩

def seenBy (view : LedgerView) (state : State) (worker : EntityUID) : Bool :=
  match view with
  | .workerLocal => if worker == workerA then state.aSeen else state.bSeen
  | .delegationShared => state.sharedSeen

def request (view : LedgerView) (state : State) (attempt : Attempt) : Request :=
  ⟨attempt.worker, attempt.action, attempt.resource, Map.make [
    ("localUsed", .prim (.int
      (CedarPooSpec.SharedBudgetExample.localUsed state.budget attempt.worker))),
    ("localMax", .prim (.int state.budget.localMax)),
    ("sharedUsed", .prim (.int state.budget.sharedUsed)),
    ("sharedMax", .prim (.int state.budget.sharedMax)),
    ("sensitiveSeen", .prim (.bool (seenBy view state attempt.worker))),
    ("intent", .prim (.string attempt.intent)),
    ("delegatedIntent", .prim (.string state.delegated))]⟩

def authorizedBy (policies : Policies) (view : LedgerView) (state : State)
    (attempt : Attempt) : Bool :=
  if attempt.worker != workerA && attempt.worker != workerB then false else
    let response := isAuthorized (request view state attempt) entities policies
    response.decision == .allow && response.erroringPolicies.isEmpty

/-- Evaluate current facts through the selected checked authorizer. -/
def authorizedWith (ready : CedarPooSpec.Functional.Ready ⟨activeModel, root, schema⟩)
    (view : LedgerView) (state : State) (attempt : Attempt) : Bool :=
  if attempt.worker != workerA && attempt.worker != workerB then false else
    (ready.authorize [request view state attempt] entities).allowed

def authorized
     (root : String) (view : LedgerView) (state : State)
    (attempt : Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.CrossAgentEgressExample.model CedarPooSpec.CrossAgentEgressExample.schema :=
      CedarPooSpec.CrossAgentEgressExample.program) : Bool :=
  match programContext.at root with
  | .error _ => false
  | .ok ready => authorizedWith ready view state attempt

def advance (state : State) (attempt : Attempt) : State :=
  if attempt.action == readAction && attempt.resource == secretDoc then
    { state with
      aSeen := state.aSeen || attempt.worker == workerA
      bSeen := state.bSeen || attempt.worker == workerB
      sharedSeen := true }
  else if attempt.action == sendAction && attempt.resource == externalEndpoint then
    { state with budget :=
        CedarPooSpec.SharedBudgetExample.advance state.budget attempt.worker }
  else state

/-- A policy-only diagnostic transition for Cedar replay cases. It does not
    consume an approval instance; Host admission uses prepare/commit below. -/
def admit
     (root : String) (view : LedgerView) (state : State)
    (attempt : Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.CrossAgentEgressExample.model CedarPooSpec.CrossAgentEgressExample.schema :=
      CedarPooSpec.CrossAgentEgressExample.program) : Bool × State :=
  let allowed := (authorized (programContext := programContext)) root view state attempt
  let next := advance state attempt
  (allowed, if allowed then { next with epoch := state.epoch + 1 } else state)

structure AdmissionTicket where
  policy : CedarPooSpec.Admission.PolicySnapshot
  view : LedgerView
  epoch : Nat
  grantId : String
  effect : BoundEffect
  deriving BEq

def prepare (activeModel : Model) (root : String) (view : LedgerView) (state : State)
    (grantId : String) (effect : BoundEffect) : Option AdmissionTicket :=
  match CedarPooSpec.Functional.prepareProgram CedarPooSpec.Functional.standard
      activeModel schema [root] with
  | .error _ => none
  | .ok active =>
      match active.at root with
      | .error _ => none
      | .ok ready =>
          if authorizedWith ready view state effect.attempt &&
              (state.authority.check grantId effect).isOk &&
              state.operations.check effect.operationId then
            some ⟨ready.policySnapshot, view, state.epoch, grantId, effect⟩
          else none

/-- A compare-and-swap admission contract. A real host must persist the
    ledger and execute this check and reservation atomically. -/
def commit (activeModel : Model) (root : String) (view : LedgerView) (state : State)
    (ticket : AdmissionTicket) (effect : BoundEffect) : Option State :=
  if ticket.policy.root != root || ticket.view != view ||
      ticket.epoch != state.epoch || ticket.effect != effect then none
  else
    match CedarPooSpec.Functional.prepareProgram CedarPooSpec.Functional.standard
        activeModel schema [root] with
    | .error _ => none
    | .ok active =>
      match active.refreshPolicy ticket.policy with
      | .error _ => none
      | .ok current =>
        if !authorizedWith current.val view state effect.attempt ||
            !state.operations.check effect.operationId then none
        else
          match state.authority.consume ticket.grantId effect with
          | .error _ => none
          | .ok authority =>
              match state.operations.admit effect.operationId with
              | none => none
              | some operations =>
                  let next := advance state effect.attempt
                  some { next with authority, operations, epoch := state.epoch + 1 }

def replayFactory
     (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.CrossAgentEgressExample.model CedarPooSpec.CrossAgentEgressExample.schema :=
      CedarPooSpec.CrossAgentEgressExample.program) :
    LeanPoo.Functional.Factory (String × LedgerView × State)
      (fun _ => State × List (Request × Bool)) :=
  LeanPoo.Functional.Factory.fold
    (fun (root, view, _) (state, rows) attempt =>
      let req := request view state attempt
      let (allowed, next) := (admit (programContext := programContext)) root view state attempt
      (next, rows ++ [(req, allowed)]))
    (fun (_, _, initial) => (initial, []))
    (attempts.map fun attempt _ => attempt)

def replay
     (root : String) (view : LedgerView) (initial : State)
    (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.CrossAgentEgressExample.model CedarPooSpec.CrossAgentEgressExample.schema :=
      CedarPooSpec.CrossAgentEgressExample.program) : List (Request × Bool) × State :=
  let (state, rows) := (replayFactory (programContext := programContext)) attempts (root, view, initial)
  (rows, state)

def decisions
     (root : String) (view : LedgerView) (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.CrossAgentEgressExample.model CedarPooSpec.CrossAgentEgressExample.schema :=
      CedarPooSpec.CrossAgentEgressExample.program) :
    List Bool := ((replay (programContext := programContext)) root view {} attempts).1.map Prod.snd

def cases : List (String × String × LedgerView × List Attempt × List Bool) := [
  ("read-only-owner-leaks-across-workers", "Read", .delegationShared,
    [readSecretA, sendB], [true, true]),
  ("history-owner-blocks-shared-egress", "History", .delegationShared,
    [readSecretA, sendB], [true, false]),
  ("intent-owner-leaves-history-gap", "Intent", .delegationShared,
    [readSecretA, sendB], [true, true]),
  ("history-owner-leaves-intent-gap", "History", .delegationShared,
    [sendB "off-task"], [true]),
  ("governed-local-ledger-still-leaks", "CrossAgentGoverned", .workerLocal,
    [readSecretA, sendB], [true, true]),
  ("governed-shared-ledger-blocks", "CrossAgentGoverned", .delegationShared,
    [readSecretA, sendB], [true, false]),
  ("governed-public-report", "CrossAgentGoverned", .delegationShared,
    [readPublicA, sendB], [true, true]),
  ("governed-off-task-send", "CrossAgentGoverned", .delegationShared,
    [sendB "off-task"], [false]),
  ("governed-shared-budget", "CrossAgentGoverned", .delegationShared,
    [sendA, sendB], [true, false]),
  ("incident-freezes-otherwise-valid-egress", "CrossAgentIncident", .delegationShared,
    [readPublicA, sendB], [true, false]),
  ("recovered-keeps-lineage-history", "CrossAgentRecovered", .delegationShared,
    [readSecretA, sendB], [true, false])]

theorem casesExact :
    cases.all (fun (_, root, view, attempts, expected) =>
      decisions root view attempts == expected) = true := by native_decide

theorem sharedLineageClosesCrossWorkerGap :
    decisions "CrossAgentGoverned" .workerLocal [readSecretA, sendB] =
      [true, true] ∧
    decisions "CrossAgentGoverned" .delegationShared [readSecretA, sendB] =
      [true, false] := by native_decide

theorem rejectedEgressDoesNotSpendBudget :
    (replay "CrossAgentGoverned" .delegationShared {}
      [readSecretA, sendB]).2.budget.sharedUsed = 0 := by native_decide

theorem survivingOwners :
    (model.compileWithProvenance "CrossAgentGoverned").toOption.map
      (·.map (fun p => p.introducedBy)) =
      some ["Base", "Shared", "Local", "Read", "Intent", "History"] := by
  native_decide

def publicSendA : BoundEffect := ⟨⟨"send-a-one"⟩, sendA, "payload-a"⟩
def publicSendB : BoundEffect := ⟨⟨"send-b-one"⟩, sendB, "payload-b"⟩
def secretReadA : BoundEffect := ⟨⟨"read-a-one"⟩, readSecretA, "document-version-1"⟩

def ticketState : State := { authority := { grants := [
  ⟨"send-a", publicSendA, 1, 0⟩,
  ⟨"send-b", publicSendB, 1, 0⟩,
  ⟨"read-a", secretReadA, 1, 0⟩] } }

private theorem firstTicketExists :
    (prepare model "CrossAgentGoverned" .delegationShared ticketState
      "send-a" publicSendA).isSome = true := by
  native_decide
private theorem secondTicketExists :
    (prepare model "CrossAgentGoverned" .delegationShared ticketState
      "send-b" publicSendB).isSome = true := by
  native_decide
private theorem readTicketExists :
    (prepare model "CrossAgentGoverned" .delegationShared ticketState
      "read-a" secretReadA).isSome = true := by
  native_decide

/-- Two tickets prepared on one budget snapshot cannot both commit. -/
theorem staleFanoutTicketRejected :
    let root := "CrossAgentGoverned"
    let first := (prepare model root .delegationShared ticketState "send-a" publicSendA).get firstTicketExists
    let second := (prepare model root .delegationShared ticketState "send-b" publicSendB).get secondTicketExists
    ((commit model root .delegationShared ticketState first publicSendA).bind fun state =>
      commit model root .delegationShared state second publicSendB) = none := by
  native_decide

/-- A checked call cannot be exchanged for different tool payload bytes. -/
theorem substitutedPayloadRejected :
    let root := "CrossAgentGoverned"
    let ticket := (prepare model root .delegationShared ticketState "send-a" publicSendA).get firstTicketExists
    commit model root .delegationShared ticketState ticket ⟨⟨"send-a-one"⟩, sendA, "substituted-payload"⟩ = none := by
  native_decide

/-- A sensitive read invalidates an earlier send ticket. Rechecking against
    shared history then refuses a new send ticket. -/
theorem sensitiveReadInvalidatesPreparedSend :
    let root := "CrossAgentGoverned"
    let sendTicket := (prepare model root .delegationShared ticketState "send-b" publicSendB).get secondTicketExists
    let readTicket := (prepare model root .delegationShared ticketState "read-a" secretReadA).get readTicketExists
    (((commit model root .delegationShared ticketState readTicket secretReadA).map fun state =>
      (commit model root .delegationShared state sendTicket publicSendB,
       prepare model root .delegationShared state "send-b" publicSendB)) ==
      some (none, none)) = true := by
  native_decide

/-- A second POO publication keeps the logical root name while adding an
    independently owned, currently nonmatching review policy. -/
def workerBReviewVeto : Policy :=
  { CedarPooSpec.SharedBudgetExample.incidentVeto with
    id := "worker-b-review-freeze",
    principalScope := .principalScope (.eq workerB) }

def reloadedModelResult : Except LeanPoo.C4.Error Model := do
  let budget := CedarPooSpec.SharedBudgetExample.model
  let read ← budget.extend "Read" "Integrated" [.extend workerRead]
  let history ← read.extend "History" "Read" [.extend lineageHistory]
  let intent ← history.extend "Intent" "Read" [.extend delegatedIntent]
  let reviewed ← intent.extend "Reviewed" "History" [.extend workerBReviewVeto]
  reviewed.mix "CrossAgentGoverned" ["Reviewed", "Intent"]

def reloadedModel : Model := reloadedModelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def reloadedProgram : CedarPooSpec.Functional.Program reloadedModel schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    reloadedModel schema (reloadedModel.modules.map (·.name)) (by native_decide)


theorem reloadedPolicyStillAllowsSend :
    (reloadedModel.compile "CrossAgentGoverned").toOption.map
      (fun policies => authorizedBy policies .delegationShared {} publicSendA.attempt) =
      some true := by native_decide

theorem reloadedPolicyFreezesWorkerB :
    (reloadedModel.compile "CrossAgentGoverned").toOption.map
      (fun policies => authorizedBy policies .delegationShared {} publicSendB.attempt) =
      some false := by native_decide

theorem reloadedRootValid :
    (CedarPooSpec.CrossAgentEgressExample.reloadedProgram.publish "CrossAgentGoverned").isOk =
      true := by native_decide

/-- Root name, ledger epoch, and effect all still match. The changed POO
    compilation alone invalidates the old admission ticket. -/
theorem reloadedPolicyRejectsPreparedTicket :
    let root := "CrossAgentGoverned"
    let ticket := (prepare model root .delegationShared ticketState "send-a" publicSendA).get firstTicketExists
    commit reloadedModel root .delegationShared ticketState ticket publicSendA = none := by
  native_decide

def reloadedPolicyRevisionDiagnosed : Bool :=
  let root := "CrossAgentGoverned"
  let ticket := (prepare model root .delegationShared ticketState "send-a" publicSendA).get firstTicketExists
  match ticket.policy.currentPolicies reloadedModel with
  | .error .changed => true
  | _ => false

theorem reloadedPolicyDiagnosesRevision :
    reloadedPolicyRevisionDiagnosed = true := by
  native_decide

theorem reloadedPolicyFreshTicketCommits :
    let root := "CrossAgentGoverned"
    (((prepare reloadedModel root .delegationShared ticketState "send-a" publicSendA).bind fun ticket =>
      commit reloadedModel root .delegationShared ticketState ticket publicSendA) ==
      some ({ budget := CedarPooSpec.SharedBudgetExample.advance {} workerA,
                authority := { grants := [
                  ⟨"send-a", publicSendA, 1, 1⟩,
                  ⟨"send-b", publicSendB, 1, 0⟩,
                  ⟨"read-a", secretReadA, 1, 0⟩] },
                operations := { admitted := [⟨"send-a-one"⟩] },
                epoch := 1 } : State)) = true := by
  native_decide

/-- The Cedar aggregate budget permits three sends, but each stable Host
    approval instance below permits only one execution. -/
def independentSendA : BoundEffect :=
  ⟨⟨"send-a-independent"⟩, sendA, "payload-a"⟩

def multiGrantState : State :=
  { budget := { localMax := 3, sharedMax := 3 }, authority := { grants := [
      ⟨"approval-one", publicSendA, 1, 0⟩,
      ⟨"approval-retry", publicSendA, 1, 0⟩,
      ⟨"approval-two", independentSendA, 1, 0⟩] } }

def firstApprovedSend : Option State := do
  let ticket ← prepare model "CrossAgentGoverned" .delegationShared
    multiGrantState "approval-one" publicSendA
  commit model "CrossAgentGoverned" .delegationShared multiGrantState ticket publicSendA

theorem consumedApprovalCannotBeReissued :
    firstApprovedSend.map (fun state =>
      (authorized "CrossAgentGoverned" .delegationShared state sendA,
       (prepare model "CrossAgentGoverned" .delegationShared state
         "approval-one" publicSendA).isNone)) = some (true, true) := by
  native_decide

theorem independentApprovalCanStillExecute :
    (firstApprovedSend.bind fun state => do
      let ticket ← prepare model "CrossAgentGoverned" .delegationShared
        state "approval-two" independentSendA
      commit model "CrossAgentGoverned" .delegationShared state ticket independentSendA).map
      (fun state => (state.budget.sharedUsed, state.authority.grants.map (·.used))) =
      some (2, [1, 0, 1]) := by
  native_decide

/-- A new approval cannot turn a retry of the same workflow operation into
    a second admission, although Cedar and the new approval still allow it. -/
theorem newApprovalCannotReplayOperation :
    firstApprovedSend.map (fun state =>
      (authorized "CrossAgentGoverned" .delegationShared state sendA,
       (state.authority.check "approval-retry" publicSendA).isOk,
       (prepare model "CrossAgentGoverned" .delegationShared state
         "approval-retry" publicSendA).isNone)) = some (true, true, true) := by
  native_decide

theorem preparedTicketCannotCommitTwice :
    ((prepare model "CrossAgentGoverned" .delegationShared multiGrantState
      "approval-one" publicSendA).bind fun ticket => do
        let state ← commit model "CrossAgentGoverned" .delegationShared
          multiGrantState ticket publicSendA
        pure (commit model "CrossAgentGoverned" .delegationShared state
          ticket publicSendA).isNone) = some true := by
  native_decide

theorem grantCannotChangeEffect :
    (prepare model "CrossAgentGoverned" .delegationShared multiGrantState
      "approval-one" ⟨⟨"send-a-one"⟩, sendA, "different-payload"⟩).isNone = true := by
  native_decide

theorem duplicateGrantIdFailsClosed :
    ((({ authority := { grants := [
        ⟨"same", publicSendA, 1, 0⟩,
        ⟨"same", publicSendA, 1, 0⟩] } } : State).authority.check
          "same" publicSendA) == .error .duplicate) = true := by
  native_decide

theorem allRootsValidate :
    ["Read", "History", "Intent", "CrossAgentGoverned",
      "CrossAgentIncident", "CrossAgentRecovered"].all (fun root =>
        (program.publish root).isOk) = true := by
  native_decide

end CedarPooSpec.CrossAgentEgressExample
