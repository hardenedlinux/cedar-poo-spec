import CedarPooSpec.SchemaJson
import CedarPooSpec.Functional.Capabilities

/-!
A finite provider-to-payer prior-authorization workflow. A clinical agent
reads one patient-bound clinical record and one billing record before an AI
draft is submitted. Independently owned policies govern patient identity,
administrative completeness, disclosure, payer requirements, and delegation.
All identifiers and facts here are synthetic host projections.
-/

namespace CedarPooSpec.PriorAuthorizationExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules

def agentType : EntityType := ⟨"PriorAuthAgent", []⟩
def recordType : EntityType := ⟨"PriorAuthRecord", []⟩
def endpointType : EntityType := ⟨"PayerEndpoint", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def agent : EntityUID := ⟨agentType, "provider-agent"⟩
def clinicalA : EntityUID := ⟨recordType, "clinical-a"⟩
def clinicalB : EntityUID := ⟨recordType, "clinical-b"⟩
def billingA : EntityUID := ⟨recordType, "billing-a"⟩
def billingB : EntityUID := ⟨recordType, "billing-b"⟩
def payer : EntityUID := ⟨endpointType, "payer-a"⟩
def readClinical : EntityUID := ⟨actionType, "read-clinical"⟩
def readBilling : EntityUID := ⟨actionType, "read-billing"⟩
def submit : EntityUID := ⟨actionType, "submit-prior-authorization"⟩

def contextType : RecordType := Map.make [
  ("expectedPatient", .required .string),
  ("clinicalSeen", .required (.bool .anyBool)),
  ("billingSeen", .required (.bool .anyBool)),
  ("codePresent", .required (.bool .anyBool)),
  ("durationPresent", .required (.bool .anyBool)),
  ("followUpPresent", .required (.bool .anyBool)),
  ("rawRecordIncluded", .required (.bool .anyBool)),
  ("payerRequirementsCurrent", .required (.bool .anyBool)),
  ("delegationActive", .required (.bool .anyBool))]
def readEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [recordType], Set.empty, contextType⟩
def submitEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [endpointType], Set.empty, contextType⟩
def recordEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("patient", .required .string), ("kind", .required .string)], none⟩
def emptyEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.empty, none⟩
def schema : Schema :=
  ⟨Map.make [(agentType, emptyEntry), (recordType, recordEntry),
      (endpointType, emptyEntry)],
    Map.make [(readClinical, readEntry), (readBilling, readEntry),
      (submit, submitEntry)]⟩
def emptyData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }
def recordData (patient kind : String) : EntityData :=
  { emptyData with attrs := Map.make [
      ("patient", .prim (.string patient)),
      ("kind", .prim (.string kind))] }
def entities : Entities := Map.make [
  (agent, emptyData), (clinicalA, recordData "patient-a" "clinical"),
  (clinicalB, recordData "patient-b" "clinical"),
  (billingA, recordData "patient-a" "billing"),
  (billingB, recordData "patient-b" "billing"), (payer, emptyData),
  (readClinical, actionSchemaEntryToEntityData readEntry),
  (readBilling, actionSchemaEntryToEntityData readEntry),
  (submit, actionSchemaEntryToEntityData submitEntry)]

def fact (name : String) : Expr := .getAttr (.var .context) name
def recordPatient : Expr := .getAttr (.var .resource) "patient"
def recordKind : Expr := .getAttr (.var .resource) "kind"
def not_ (body : Expr) : Expr := .unaryApp .not body
def andAll : List Expr → Expr
  | [] => .lit (.bool true)
  | [body] => body
  | body :: rest => .and body (andAll rest)
def policy (id : String) (effect : Effect) (action : ActionScope)
    (resource : Scope) (body : Expr) : Policy :=
  { id, effect,
    principalScope := .principalScope .any,
    actionScope := action,
    resourceScope := .resourceScope resource,
    condition := [{ kind := .when, body }] }

def clinicalPermit : Policy :=
  policy "read-clinical" .permit (.actionScope (.eq readClinical)) .any
    (.binaryApp .eq recordKind (.lit (.string "clinical")))
def billingPermit : Policy :=
  policy "read-billing" .permit (.actionScope (.eq readBilling)) .any
    (.binaryApp .eq recordKind (.lit (.string "billing")))
def submitPermit : Policy :=
  policy "submit-draft" .permit (.actionScope (.eq submit)) (.eq payer)
    (.lit (.bool true))

/-- The identity owner checks each record at the read boundary. -/
def wrongPatientVeto : Policy :=
  policy "patient-misbinding" .forbid (.actionInAny [readClinical, readBilling]) .any
    (not_ (.binaryApp .eq (fact "expectedPatient") recordPatient))
def missingClinicalVeto : Policy :=
  policy "clinical-evidence-missing" .forbid (.actionScope (.eq submit)) (.eq payer)
    (not_ (fact "clinicalSeen"))
def missingBillingVeto : Policy :=
  policy "billing-evidence-missing" .forbid (.actionScope (.eq submit)) (.eq payer)
    (not_ (fact "billingSeen"))
/-- The administrative owner reflects gaps observed in the 2026 letter study. -/
def incompleteLetterVeto : Policy :=
  policy "administrative-fields-missing" .forbid (.actionScope (.eq submit)) (.eq payer)
    (not_ (andAll [fact "codePresent", fact "durationPresent",
      fact "followUpPresent"]))
def rawDisclosureVeto : Policy :=
  policy "raw-record-in-draft" .forbid (.actionScope (.eq submit)) (.eq payer)
    (fact "rawRecordIncluded")
def stalePayerVeto : Policy :=
  policy "payer-requirements-stale" .forbid (.actionScope (.eq submit)) (.eq payer)
    (not_ (fact "payerRequirementsCurrent"))
def expiredDelegationVeto : Policy :=
  policy "delegation-expired" .forbid (.actionInAny [readClinical, readBilling, submit])
    .any (not_ (fact "delegationActive"))
def incidentVeto : Policy :=
  policy "submission-incident-freeze" .forbid (.actionScope (.eq submit)) (.eq payer)
    (.lit (.bool true))

/-- Positive final grants make missing required context fail closed even when
    Cedar skips a veto that errors on that same missing field. -/
def boundClinicalPermit : Policy :=
  let body := andAll [
    .binaryApp .eq recordKind (.lit (.string "clinical")),
    .binaryApp .eq (fact "expectedPatient") recordPatient,
    fact "delegationActive"]
  { clinicalPermit with condition := [{ kind := .when, body }] }
def boundBillingPermit : Policy :=
  let body := andAll [
    .binaryApp .eq recordKind (.lit (.string "billing")),
    .binaryApp .eq (fact "expectedPatient") recordPatient,
    fact "delegationActive"]
  { billingPermit with condition := [{ kind := .when, body }] }
def boundSubmitPermit : Policy :=
  let body := andAll [fact "clinicalSeen", fact "billingSeen",
    fact "codePresent", fact "durationPresent", fact "followUpPresent",
    not_ (fact "rawRecordIncluded"), fact "payerRequirementsCurrent",
    fact "delegationActive"]
  { submitPermit with condition := [{ kind := .when, body }] }

/-- Five owners extend the same baseline, then C4-combine their restrictions. -/
def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [.extend clinicalPermit, .extend billingPermit,
        .extend submitPermit] }] }
  let identity ← base.extend "Identity" "Base"
    [.extend wrongPatientVeto, .extend missingClinicalVeto]
  let administration ← identity.extend "Administration" "Base"
    [.extend missingBillingVeto, .extend incompleteLetterVeto]
  let privacy ← administration.extend "Privacy" "Base"
    [.extend rawDisclosureVeto]
  let payerRules ← privacy.extend "PayerRules" "Base"
    [.extend stalePayerVeto]
  let temporal ← payerRules.extend "Temporal" "Base"
    [.extend expiredDelegationVeto]
  let combined ← temporal.mix "Combined"
    ["Identity", "Administration", "Privacy", "PayerRules", "Temporal"]
  let governed ← combined.extend "Governed" "Combined"
    [.overlay boundClinicalPermit, .overlay boundBillingPermit,
      .overlay boundSubmitPermit]
  let incident ← governed.extend "Incident" "Governed"
    [.extend incidentVeto]
  incident.extend "Recovered" "Incident" [.remove incidentVeto.id]

def model : Model := modelResult.toOption.get (by native_decide)

def roots : List String :=
  ["Base", "Identity", "Administration", "Privacy", "PayerRules", "Temporal",
    "Combined", "Governed", "Incident", "Recovered"]

def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard model schema roots
    (by native_decide)

structure State where
  expectedPatient : String := "patient-a"
  clinicalSeen : Bool := false
  billingSeen : Bool := false
  codePresent : Bool := true
  durationPresent : Bool := true
  followUpPresent : Bool := true
  rawRecordIncluded : Bool := false
  payerRequirementsCurrent : Bool := true
  delegationActive : Bool := true

structure Attempt where
  action : EntityUID
  resource : EntityUID

def clinicalRead : Attempt := ⟨readClinical, clinicalA⟩
def swappedClinicalRead : Attempt := ⟨readClinical, clinicalB⟩
def billingRead : Attempt := ⟨readBilling, billingA⟩
def swappedBillingRead : Attempt := ⟨readBilling, billingB⟩
def payerSubmit : Attempt := ⟨submit, payer⟩

def request (state : State) (attempt : Attempt) : Request :=
  ⟨agent, attempt.action, attempt.resource, Map.make [
    ("expectedPatient", .prim (.string state.expectedPatient)),
    ("clinicalSeen", .prim (.bool state.clinicalSeen)),
    ("billingSeen", .prim (.bool state.billingSeen)),
    ("codePresent", .prim (.bool state.codePresent)),
    ("durationPresent", .prim (.bool state.durationPresent)),
    ("followUpPresent", .prim (.bool state.followUpPresent)),
    ("rawRecordIncluded", .prim (.bool state.rawRecordIncluded)),
    ("payerRequirementsCurrent", .prim (.bool state.payerRequirementsCurrent)),
    ("delegationActive", .prim (.bool state.delegationActive))]⟩

def authorized
     (root : String) (state : State) (attempt : Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PriorAuthorizationExample.model CedarPooSpec.PriorAuthorizationExample.schema :=
      CedarPooSpec.PriorAuthorizationExample.program) : Bool :=
  match programContext.authorize root [request state attempt] entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

def advance (state : State) (attempt : Attempt) : State :=
  { state with
    clinicalSeen := state.clinicalSeen ||
      (attempt.action == readClinical && attempt.resource == clinicalA),
    billingSeen := state.billingSeen ||
      (attempt.action == readBilling && attempt.resource == billingA) }

def replayFactory
     (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PriorAuthorizationExample.model CedarPooSpec.PriorAuthorizationExample.schema :=
      CedarPooSpec.PriorAuthorizationExample.program) : LeanPoo.Functional.Factory (String × State)
    (fun _ => State × List (Request × Bool)) :=
  LeanPoo.Functional.Factory.fold
    (fun (root, _) (state, rows) attempt =>
      let req := request state attempt
      let allowed := (authorized (programContext := programContext)) root state attempt
      (if allowed then advance state attempt else state, rows ++ [(req, allowed)]))
    (fun (_, initial) => (initial, []))
    (attempts.map fun attempt _ => attempt)

def replay
     (root : String) (initial : State) (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PriorAuthorizationExample.model CedarPooSpec.PriorAuthorizationExample.schema :=
      CedarPooSpec.PriorAuthorizationExample.program) :
    List (Request × Bool) × State :=
  let (state, rows) := (replayFactory (programContext := programContext)) attempts (root, initial)
  (rows, state)

def decisions
     (root : String) (initial : State) (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PriorAuthorizationExample.model CedarPooSpec.PriorAuthorizationExample.schema :=
      CedarPooSpec.PriorAuthorizationExample.program) :
    List Bool := ((replay (programContext := programContext)) root initial attempts).1.map Prod.snd

def afterEvidenceRevoked
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PriorAuthorizationExample.model CedarPooSpec.PriorAuthorizationExample.schema :=
      CedarPooSpec.PriorAuthorizationExample.program) : State :=
  { ((replay (programContext := programContext)) "Governed" {} [clinicalRead, billingRead]).2 with
    delegationActive := false }

def cases
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PriorAuthorizationExample.model CedarPooSpec.PriorAuthorizationExample.schema :=
      CedarPooSpec.PriorAuthorizationExample.program) : List (String × String × State × List Attempt × List Bool) := [
  ("baseline-submits-without-evidence", "Base", {}, [payerSubmit], [true]),
  ("identity-owner-misses-admin", "Identity", {},
    [clinicalRead, billingRead, payerSubmit], [true, true, true]),
  ("baseline-reads-swapped-patient", "Base", {},
    [swappedClinicalRead], [true]),
  ("baseline-wrong-patient-propagates", "Base", {},
    [swappedClinicalRead, billingRead, payerSubmit], [true, true, true]),
  ("governed-wrong-patient-stops-submission", "Governed", {},
    [swappedClinicalRead, billingRead, payerSubmit], [false, true, false]),
  ("swapped-clinical-patient", "Governed", {},
    [swappedClinicalRead], [false]),
  ("swapped-billing-patient", "Governed", {},
    [swappedBillingRead], [false]),
  ("complete-provider-to-payer", "Governed", {},
    [clinicalRead, billingRead, payerSubmit], [true, true, true]),
  ("missing-clinical-evidence", "Governed", {},
    [billingRead, payerSubmit], [true, false]),
  ("missing-billing-evidence", "Governed", {},
    [clinicalRead, payerSubmit], [true, false]),
  ("missing-billing-code", "Governed", { codePresent := false },
    [clinicalRead, billingRead, payerSubmit], [true, true, false]),
  ("missing-duration", "Governed", { durationPresent := false },
    [clinicalRead, billingRead, payerSubmit], [true, true, false]),
  ("missing-follow-up", "Governed", { followUpPresent := false },
    [clinicalRead, billingRead, payerSubmit], [true, true, false]),
  ("raw-record-in-draft", "Governed", { rawRecordIncluded := true },
    [clinicalRead, billingRead, payerSubmit], [true, true, false]),
  ("stale-payer-requirements", "Governed",
    { payerRequirementsCurrent := false },
    [clinicalRead, billingRead, payerSubmit], [true, true, false]),
  ("delegation-revoked-after-reads", "Governed", (afterEvidenceRevoked (programContext := programContext)),
    [payerSubmit], [false]),
  ("incident-freezes-valid-submission", "Incident", {},
    [clinicalRead, billingRead, payerSubmit], [true, true, false]),
  ("recovered-restores-valid-submission", "Recovered", {},
    [clinicalRead, billingRead, payerSubmit], [true, true, true]),
  ("recovered-keeps-privacy", "Recovered", { rawRecordIncluded := true },
    [clinicalRead, billingRead, payerSubmit], [true, true, false])]

theorem casesExact :
    cases.all (fun (_, root, state, attempts, expected) =>
      decisions root state attempts == expected) = true := by native_decide

theorem composedOwnersPresent :
    ["Identity", "Administration", "Privacy", "PayerRules", "Temporal"].all
      (fun owner =>
        ((model.compileWithProvenance "Governed").toOption.get
          (by native_decide)).any (fun p => p.introducedBy == owner)) = true := by
  native_decide

theorem recoveryKeepsGovernedPolicies :
    (model.compile "Recovered" == model.compile "Governed") = true := by
  native_decide

def missingDisclosureFact : Request :=
  let req := request
    { clinicalSeen := true, billingSeen := true } payerSubmit
  let remaining := req.context.toList.filter
    (fun (name, _) => name != "rawRecordIncluded")
  { req with context := Map.make remaining }

theorem missingDisclosureFactCannotGrant :
    (match model.compile "Governed" with
    | .error _ => false
    | .ok policies =>
        (isAuthorized missingDisclosureFact entities policies).decision == .deny) =
      true := by native_decide

theorem allRootsValidate :
    roots.all (fun root => (program.publish root).isOk) =
        true := by native_decide

end CedarPooSpec.PriorAuthorizationExample
