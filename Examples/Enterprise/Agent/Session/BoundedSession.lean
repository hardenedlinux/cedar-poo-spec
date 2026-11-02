import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Revision
import CedarPooSpec.PolicyJson

/-!
A long-running agent session with a trusted action ledger. Each Cedar request
is checked before the host advances that ledger. The model does not inspect
prompts or authenticate the host's session facts.
-/

namespace CedarPooSpec.BoundedSessionExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Soundness CedarPooSpec.PolicyValidation LeanPoo.Proof

def agentType : EntityType := ⟨"Agent", []⟩
def documentType : EntityType := ⟨"Document", []⟩
def endpointType : EntityType := ⟨"Endpoint", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def agent : EntityUID := ⟨agentType, "research-agent"⟩
def publicDoc : EntityUID := ⟨documentType, "public-brief"⟩
def secretDoc : EntityUID := ⟨documentType, "restricted-brief"⟩
def internalEndpoint : EntityUID := ⟨endpointType, "internal-review"⟩
def externalEndpoint : EntityUID := ⟨endpointType, "external-report"⟩
def readAction : EntityUID := ⟨actionType, "read"⟩
def sendAction : EntityUID := ⟨actionType, "send"⟩

def emptyEntry : EntitySchemaEntry := .standard ⟨Set.empty, Map.empty, none⟩
def documentEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [("sensitive", .required (.bool .anyBool))], none⟩
def endpointEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [("external", .required (.bool .anyBool))], none⟩
def contextType : RecordType := Map.make [
  ("intent", .required .string),
  ("delegatedIntent", .required .string),
  ("sensitiveSeen", .required (.bool .anyBool)),
  ("usedExports", .required .int),
  ("maxExports", .required .int)]
def readEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [documentType], Set.empty, contextType⟩
def sendEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [endpointType], Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [(agentType, emptyEntry), (documentType, documentEntry),
      (endpointType, endpointEntry)],
    Map.make [(readAction, readEntry), (sendAction, sendEntry)]⟩

def emptyData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }
def documentData (sensitive : Bool) : EntityData :=
  { emptyData with attrs := Map.make [("sensitive", .prim (.bool sensitive))] }
def endpointData (external : Bool) : EntityData :=
  { emptyData with attrs := Map.make [("external", .prim (.bool external))] }
def entities : Entities := Map.make [
  (agent, emptyData), (publicDoc, documentData false),
  (secretDoc, documentData true),
  (internalEndpoint, endpointData false),
  (externalEndpoint, endpointData true),
  (readAction, actionSchemaEntryToEntityData readEntry),
  (sendAction, actionSchemaEntryToEntityData sendEntry)]

def ctx (name : String) : Expr := .getAttr (.var .context) name
def resourceFact (name : String) : Expr := .getAttr (.var .resource) name
def policy (id : String) (effect : Effect) (action : EntityUID)
    (body : Expr) : Policy :=
  { id, effect,
    principalScope := .principalScope (.eq agent),
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body }] }

def readPermit : Policy :=
  policy "agent-read" .permit readAction (.lit (.bool true))
def sendPermit : Policy :=
  policy "agent-send" .permit sendAction (.lit (.bool true))
def intentVeto : Policy :=
  policy "delegated-intent" .forbid sendAction
    (.unaryApp .not (.binaryApp .eq (ctx "intent") (ctx "delegatedIntent")))
def historyVeto : Policy :=
  policy "read-then-egress" .forbid sendAction
    (.and (ctx "sensitiveSeen") (resourceFact "external"))
def budgetVeto : Policy :=
  policy "session-export-budget" .forbid sendAction
    (.and (resourceFact "external")
      (.unaryApp .not (.binaryApp .less (ctx "usedExports") (ctx "maxExports"))))
def incidentVeto : Policy :=
  policy "incident-egress-freeze" .forbid sendAction (resourceFact "external")

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model :=
    { modules := [{ name := "Base", edits := [.extend readPermit, .extend sendPermit] }] }
  let intent ← base.extend "Intent" "Base" [.extend intentVeto]
  let history ← intent.extend "History" "Base" [.extend historyVeto]
  let budget ← history.extend "Budget" "Base" [.extend budgetVeto]
  let integrated ← budget.mix "Integrated" ["Intent", "History", "Budget"]
  let incident ← integrated.extend "Incident" "Integrated" [.extend incidentVeto]
  incident.extend "Recovered" "Incident" [.remove incidentVeto.id]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

/-- The host owns this ledger and serializes admission and updates. -/

structure Session where
  sensitiveSeen : Bool := false
  usedExports : Int64 := 0
  maxExports : Int64 := 1
  delegatedIntent : String := "report"
  deriving BEq, DecidableEq, Repr

structure Attempt where
  action : EntityUID
  resource : EntityUID
  intent : String := "report"

def readPublic : Attempt := ⟨readAction, publicDoc, "report"⟩
def readSecret : Attempt := ⟨readAction, secretDoc, "report"⟩
def sendExternal (intent := "report") : Attempt :=
  ⟨sendAction, externalEndpoint, intent⟩
def sendInternal (intent := "report") : Attempt :=
  ⟨sendAction, internalEndpoint, intent⟩

def request (session : Session) (attempt : Attempt) : Request :=
  ⟨agent, attempt.action, attempt.resource, Map.make [
    ("intent", .prim (.string attempt.intent)),
    ("delegatedIntent", .prim (.string session.delegatedIntent)),
    ("sensitiveSeen", .prim (.bool session.sensitiveSeen)),
    ("usedExports", .prim (.int session.usedExports)),
    ("maxExports", .prim (.int session.maxExports))]⟩

def authorized
     (root : String) (session : Session) (attempt : Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.BoundedSessionExample.model CedarPooSpec.BoundedSessionExample.schema :=
      CedarPooSpec.BoundedSessionExample.program) : Bool :=
  match programContext.response root (request session attempt) entities with
  | .error _ => false
  | .ok response =>
      response.decision == .allow && response.erroringPolicies.isEmpty

/-- A rejected action never advances the trusted ledger. -/
def advance (session : Session) (attempt : Attempt) : Session :=
  if attempt.action == readAction && attempt.resource == secretDoc then
    { session with sensitiveSeen := true }
  else if attempt.action == sendAction && attempt.resource == externalEndpoint then
    { session with usedExports := session.usedExports + 1 }
  else session

/-- Record the exact request before each decision, then update on Allow. -/
def replay
     (root : String) (initial : Session) (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.BoundedSessionExample.model CedarPooSpec.BoundedSessionExample.schema :=
      CedarPooSpec.BoundedSessionExample.program) :
    List (Request × Bool) × Session :=
  let (state, rows) := attempts.foldl (fun (state, rows) attempt =>
    let req := request state attempt
    let allowed := (authorized (programContext := programContext)) root state attempt
    let next := if allowed then advance state attempt else state
    (next, rows ++ [(req, allowed)])) (initial, [])
  (rows, state)

def decisions
     (root : String) (initial : Session) (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.BoundedSessionExample.model CedarPooSpec.BoundedSessionExample.schema :=
      CedarPooSpec.BoundedSessionExample.program) :
    List Bool := ((replay (programContext := programContext)) root initial attempts).1.map Prod.snd

def cases : List (String × String × Session × List Attempt × List Bool) := [
  ("legacy-read-then-egress", "Base", {}, [readSecret, sendExternal], [true, true]),
  ("intent-alone-still-leaks", "Intent", {}, [readSecret, sendExternal], [true, true]),
  ("history-alone-misses-task", "History", {}, [sendExternal "off-task"], [true]),
  ("budget-alone-first-leak", "Budget", {}, [readSecret, sendExternal], [true, true]),
  ("integrated-stops-composed-leak", "Integrated", {},
    [readSecret, sendExternal], [true, false]),
  ("integrated-allows-public-report", "Integrated", {},
    [readPublic, sendExternal], [true, true]),
  ("integrated-denies-off-task", "Integrated", {}, [sendExternal "off-task"], [false]),
  ("integrated-bounds-retries", "Integrated", {},
    [readPublic, sendExternal, sendExternal], [true, true, false]),
  ("automated-probe-budget", "Integrated", {},
    List.replicate 32 sendExternal, true :: List.replicate 31 false),
  ("denial-does-not-spend-budget", "Integrated", {},
    [sendExternal "off-task", sendExternal], [false, true]),
  ("sensitive-internal-review", "Integrated", {},
    [readSecret, sendInternal], [true, true]),
  ("incident-freezes-external", "Incident", {},
    [readPublic, sendExternal], [true, false]),
  ("incident-keeps-internal", "Incident", {}, [sendInternal], [true]),
  ("recovered-restores-public", "Recovered", {},
    [readPublic, sendExternal], [true, true]),
  ("recovery-retains-history-rule", "Recovered", {},
    [readSecret, sendExternal], [true, false])]

theorem casesExact :
    cases.all (fun (_, root, initial, attempts, expected) =>
      decisions root initial attempts == expected) = true := by native_decide

/-- Repeating a denied proposal cannot exhaust or bypass the session ledger. -/
theorem repeatedProbesBounded :
    decisions "Integrated" {} (List.replicate 32 sendExternal) =
      true :: List.replicate 31 false := by native_decide

theorem deniedActionLeavesState :
    ((replay "Integrated" {} [sendExternal "off-task"]).2 == ({} : Session)) = true := by
  native_decide

def rootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.BoundedSessionExample.model CedarPooSpec.BoundedSessionExample.schema :=
      CedarPooSpec.BoundedSessionExample.program) : Bool :=
  ["Base", "Intent", "History", "Budget", "Integrated", "Incident",
    "Recovered"].all fun root => (programContext.publish root).isOk
theorem rootsValidatedExact : rootsValidated = true := by native_decide

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
theorem recoveredPolicies :
    (model.compile "Recovered" == model.compile "Integrated") = true := by native_decide

def witness : Request := request {} sendExternal
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

end CedarPooSpec.BoundedSessionExample
