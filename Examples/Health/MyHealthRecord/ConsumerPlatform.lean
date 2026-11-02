import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.SchemaJson
import CedarPooSpec.Governance.Veto
import CedarPooSpec.Vertical.Health.DisclosureChannel
import CedarPooSpec.Vertical.Health.FHIR.ConsumerAccess

/-!
A synthetic consumer app using My Health Record FHIR Gateway interaction model
#4: the consumer app, its intermediary, and an optional AI summary service.
The Australian gateway does not supply the AI service or these Cedar policies.
The Host owns myGov/OAuth, consent state, FHIR bytes, storage, and audit.
-/

namespace CedarPooSpec.MyHealthRecordExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Governance CedarPooSpec.Vertical.Health
open CedarPooSpec.Vertical.Health.FHIR

def appType : EntityType := ⟨"ConsumerApp", []⟩
def recordType : EntityType := ⟨"FhirRecord", []⟩
def endpointType : EntityType := ⟨"ConsumerOutput", []⟩
def actionType : EntityType := ⟨"Action", []⟩

def app : EntityUID := ⟨appType, "patient-app"⟩
def assistant : EntityUID := ⟨appType, "summary-assistant"⟩
def summaryA : EntityUID := ⟨recordType, "summary-a"⟩
def summaryB : EntityUID := ⟨recordType, "summary-b"⟩
def medicationA : EntityUID := ⟨recordType, "medications-a"⟩
def outputA : EntityUID := ⟨endpointType, "patient-output"⟩
def fetch : EntityUID := ⟨actionType, "fetch-fhir"⟩
def summarize : EntityUID := ⟨actionType, "summarize"⟩
def release : EntityUID := ⟨actionType, "release-summary"⟩
def purge : EntityUID := ⟨actionType, "purge-local-data"⟩

def appEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("patient", .required .string), ("kind", .required .string)], none⟩
def recordEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("patient", .required .string), ("kind", .required .string)], none⟩
def endpointEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [("patient", .required .string)], none⟩
def contextType : RecordType := Map.make [
  ("subjectPatient", .required .string),
  ("purpose", .required .string),
  ("payloadClass", .required .string),
  ("patientMatches", .required (.bool .anyBool)),
  ("delegationActive", .required (.bool .anyBool)),
  ("oauthActive", .required (.bool .anyBool)),
  ("sessionActive", .required (.bool .anyBool)),
  ("withinInactivityWindow", .required (.bool .anyBool)),
  ("appAccessActive", .required (.bool .anyBool)),
  ("fetchedDigestMatches", .required (.bool .anyBool)),
  ("summaryDigestMatches", .required (.bool .anyBool)),
  ("modelApproved", .required (.bool .anyBool)),
  ("humanReviewed", .required (.bool .anyBool)),
  ("auditReady", .required (.bool .anyBool))]
def recordAction : ActionSchemaEntry :=
  ⟨Set.make [appType], Set.make [recordType], Set.empty, contextType⟩
def outputAction : ActionSchemaEntry :=
  ⟨Set.make [appType], Set.make [endpointType], Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [(appType, appEntry), (recordType, recordEntry),
    (endpointType, endpointEntry)],
   Map.make [(fetch, recordAction), (summarize, recordAction),
    (release, outputAction), (purge, outputAction)]⟩

def data (patient kind : String) : EntityData :=
  { attrs := Map.make [("patient", .prim (.string patient)),
      ("kind", .prim (.string kind))],
    ancestors := Set.empty, tags := Map.empty }
def endpointData (patient : String) : EntityData :=
  { attrs := Map.make [("patient", .prim (.string patient))],
    ancestors := Set.empty, tags := Map.empty }
def entities : Entities := Map.make [
  (app, data "patient-a" "app"),
  (assistant, data "patient-a" "agent"),
  (summaryA, data "patient-a" "personal-health-summary"),
  (summaryB, data "patient-b" "personal-health-summary"),
  (medicationA, data "patient-a" "medication-list"),
  (outputA, endpointData "patient-a"),
  (fetch, actionSchemaEntryToEntityData recordAction),
  (summarize, actionSchemaEntryToEntityData recordAction),
  (release, actionSchemaEntryToEntityData outputAction),
  (purge, actionSchemaEntryToEntityData outputAction)]

def attr (source : Var) (name : String) : Expr := .getAttr (.var source) name
def fact (name : String) : Expr := attr .context name
def eq (left right : Expr) : Expr := .binaryApp .eq left right
def string (value : String) : Expr := .lit (.string value)
def not (body : Expr) : Expr := .unaryApp .not body
def kindIs (source : Var) (value : String) : Expr :=
  eq (attr source "kind") (string value)

def permit (id : String) (action : EntityUID) (body : Expr) : Policy :=
  { id, effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body }] }

def fhirRead : ResourceRead :=
  { policyId := "fetch-personal-summary", action := fetch,
    principalKind := "app", resourceKind := "personal-health-summary",
    purpose := "self-care" }
def fetchPermit : Policy := fhirRead.policy
def purgePermit : Policy :=
  permit "purge-after-revocation" purge (kindIs .principal "app")
def legacyAgentPermit : Policy :=
  permit "legacy-agent-read" summarize (.lit (.bool true))
def summaryPermit : Policy :=
  permit "approved-summary" summarize
    (.and (kindIs .principal "agent")
      (.and (kindIs .resource "personal-health-summary")
        (.and (fact "fetchedDigestMatches") (fact "modelApproved"))))

def disclosure : DisclosureChannel :=
  { policyId := "release-reviewed-summary", action := release,
    destination := outputA, purpose := "self-care", payloadClass := "minimal-summary" }
def identityControl : Veto :=
  (PatientBoundary.control {
    policyId := "patient-boundary", actionScope := .actionScope .any })
def oauthControl : Veto :=
  (ConsumerSession.control {
    policyId := "stale-oauth-session", action := fetch })
def revocationControl : Veto :=
  (RevocableUse.control {
    policyId := "revoked-app-access", actions := [fetch, summarize, release] })
def delegationControl : Veto :=
  { policyId := "expired-summary-delegation",
    actionScope := .actionScope (.eq release),
    denyWhen := not (fact "delegationActive") }
def releaseControl : Veto :=
  { policyId := "unreviewed-or-unaudited-summary",
    actionScope := .actionScope (.eq release),
    denyWhen := .or (not (fact "humanReviewed"))
      (.or (not (fact "auditReady"))
        (.or (not (fact "fetchedDigestMatches"))
          (not (fact "summaryDigestMatches")))) }
def incidentControl : Veto :=
  { policyId := "agent-incident",
    actionScope := .actionInAny [summarize, release],
    denyWhen := .lit (.bool true) }

/-- Consent, session, data release, and agent owners form a C4 diamond. -/
def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [
      fhirRead.introduce, .extend purgePermit, .extend legacyAgentPermit] }] }
  let identity ← base.extend "Identity" "Base" [identityControl.edit .introduce]
  let session ← identity.extend "Session" "Base" [oauthControl.edit .introduce]
  let consent ← session.extend "Consent" "Base" [revocationControl.edit .introduce]
  let agent ← consent.extend "Agent" "Base" [
    .extend summaryPermit, disclosure.introduce,
    delegationControl.edit .introduce, releaseControl.edit .introduce]
  let integrated ← agent.mix "ConsumerPlatform"
    ["Identity", "Session", "Consent", "Agent"]
    [disclosure.strengthen, .remove legacyAgentPermit.id]
  let incident ← integrated.extend "AgentIncident" "ConsumerPlatform"
    [incidentControl.edit .introduce]
  incident.extend "Recovered" "AgentIncident"
    [incidentControl.edit .withdraw]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)


structure Facts where
  subjectPatient : String := "patient-a"
  purpose : String := "self-care"
  payloadClass : String := "minimal-summary"
  patientMatches : Bool := true
  delegationActive : Bool := true
  oauthActive : Bool := true
  sessionActive : Bool := true
  withinInactivityWindow : Bool := true
  appAccessActive : Bool := true
  fetchedDigestMatches : Bool := true
  summaryDigestMatches : Bool := true
  modelApproved : Bool := true
  humanReviewed : Bool := true
  auditReady : Bool := true

def request (actor action resource : EntityUID) (facts : Facts := {}) : Request :=
  ⟨actor, action, resource, Map.make [
    ("subjectPatient", .prim (.string facts.subjectPatient)),
    ("purpose", .prim (.string facts.purpose)),
    ("payloadClass", .prim (.string facts.payloadClass)),
    ("patientMatches", .prim (.bool facts.patientMatches)),
    ("delegationActive", .prim (.bool facts.delegationActive)),
    ("oauthActive", .prim (.bool facts.oauthActive)),
    ("sessionActive", .prim (.bool facts.sessionActive)),
    ("withinInactivityWindow", .prim (.bool facts.withinInactivityWindow)),
    ("appAccessActive", .prim (.bool facts.appAccessActive)),
    ("fetchedDigestMatches", .prim (.bool facts.fetchedDigestMatches)),
    ("summaryDigestMatches", .prim (.bool facts.summaryDigestMatches)),
    ("modelApproved", .prim (.bool facts.modelApproved)),
    ("humanReviewed", .prim (.bool facts.humanReviewed)),
    ("auditReady", .prim (.bool facts.auditReady))]⟩

def cases : List (String × String × Request × Decision) := [
  ("legacy-agent-risk", "Base", request assistant summarize summaryA
    { modelApproved := false }, .allow),
  ("fetch-summary", "ConsumerPlatform", request app fetch summaryA, .allow),
  ("fetch-other-patient", "ConsumerPlatform", request app fetch summaryB, .deny),
  ("fetch-other-document-class", "ConsumerPlatform", request app fetch medicationA, .deny),
  ("fetch-wrong-purpose", "ConsumerPlatform", request app fetch summaryA
    { purpose := "marketing" }, .deny),
  ("fetch-expired-oauth", "ConsumerPlatform", request app fetch summaryA
    { oauthActive := false }, .deny),
  ("fetch-expired-session", "ConsumerPlatform", request app fetch summaryA
    { sessionActive := false }, .deny),
  ("fetch-six-month-inactivity", "ConsumerPlatform", request app fetch summaryA
    { withinInactivityWindow := false }, .deny),
  ("summarize-approved", "ConsumerPlatform", request assistant summarize summaryA, .allow),
  ("summarize-unapproved-model", "ConsumerPlatform", request assistant summarize summaryA
    { modelApproved := false }, .deny),
  ("summarize-stale-source", "ConsumerPlatform", request assistant summarize summaryA
    { fetchedDigestMatches := false }, .deny),
  ("release-reviewed", "ConsumerPlatform", request app release outputA, .allow),
  ("release-unreviewed", "ConsumerPlatform", request app release outputA
    { humanReviewed := false }, .deny),
  ("release-no-audit", "ConsumerPlatform", request app release outputA
    { auditReady := false }, .deny),
  ("release-stale-summary", "ConsumerPlatform", request app release outputA
    { summaryDigestMatches := false }, .deny),
  ("release-expired-delegation", "ConsumerPlatform", request app release outputA
    { delegationActive := false }, .deny),
  ("release-broad-payload", "ConsumerPlatform", request app release outputA
    { payloadClass := "raw-record" }, .deny),
  ("revoked-fetch", "ConsumerPlatform", request app fetch summaryA
    { appAccessActive := false }, .deny),
  ("revoked-summary", "ConsumerPlatform", request assistant summarize summaryA
    { appAccessActive := false }, .deny),
  ("revoked-release", "ConsumerPlatform", request app release outputA
    { appAccessActive := false }, .deny),
  ("purge-after-revocation", "ConsumerPlatform", request app purge outputA
    { appAccessActive := false }, .allow),
  ("incident-blocks-agent", "AgentIncident", request assistant summarize summaryA, .deny),
  ("incident-keeps-consumer-read", "AgentIncident", request app fetch summaryA, .allow),
  ("incident-keeps-purge", "AgentIncident", request app purge outputA
    { appAccessActive := false }, .allow),
  ("recovery-restores-agent", "Recovered", request assistant summarize summaryA, .allow),
  ("recovery-keeps-revocation", "Recovered", request assistant summarize summaryA
    { appAccessActive := false }, .deny)]

def observed
     (root : String) (req : Request)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MyHealthRecordExample.model CedarPooSpec.MyHealthRecordExample.schema :=
      CedarPooSpec.MyHealthRecordExample.program) : Decision × Bool :=
  match programContext.response root req entities with
  | .error _ => (.deny, false)
  | .ok answer =>
    (answer.decision, answer.erroringPolicies.isEmpty)

def casesConform
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MyHealthRecordExample.model CedarPooSpec.MyHealthRecordExample.schema :=
      CedarPooSpec.MyHealthRecordExample.program) : Bool := cases.all fun (_, root, req, expected) =>
  let answer := (observed (programContext := programContext)) root req
  answer.1 == expected && answer.2
theorem casesConformFully : casesConform = true := by native_decide

theorem incidentChangesOnePolicy :
    ((model.compileRevision "ConsumerPlatform" "AgentIncident").toOption.get
      (by native_decide)).changedPolicyIds = ["agent-incident"] := by native_decide
theorem recoveryRestoresIntegrated :
    (model.compile "Recovered" == model.compile "ConsumerPlatform") = true := by native_decide
theorem legacyPermitRemoved :
    ((model.compile "ConsumerPlatform").toOption.get (by native_decide)).all
      (fun policy => policy.id != legacyAgentPermit.id) = true := by native_decide

end CedarPooSpec.MyHealthRecordExample
