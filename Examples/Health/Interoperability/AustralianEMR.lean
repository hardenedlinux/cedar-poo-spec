import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.SchemaJson
import CedarPooSpec.Governance.Veto
import CedarPooSpec.Vertical.Health.Region.Australia

/-!
Synthetic eMR discharge-document upload. An external FHIR/terminology service
and the Host validate content, identifiers, and versioned profiles. Cedar
decides whether this particular patient-bound upload may proceed.
-/

namespace CedarPooSpec.AustralianEMRExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Governance
open CedarPooSpec.Vertical.Health.ClinicalExchange
open CedarPooSpec.Vertical.Health.Region.Australia

def serviceType : EntityType := ⟨"EMRService", []⟩
def documentType : EntityType := ⟨"ClinicalDocument", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def hospital : EntityUID := ⟨serviceType, "hospital-emr"⟩
def agent : EntityUID := ⟨serviceType, "draft-agent"⟩
def dischargeA : EntityUID := ⟨documentType, "discharge-a"⟩
def dischargeB : EntityUID := ⟨documentType, "discharge-b"⟩
def medicationA : EntityUID := ⟨documentType, "medication-a"⟩
def upload : EntityUID := ⟨actionType, "upload-clinical-document"⟩

def contextType : RecordType := Map.make [
  ("subjectPatient", .required .string),
  ("purpose", .required .string),
  ("ihiVerified", .required (.bool .anyBool)),
  ("patientDeclinedUpload", .required (.bool .anyBool)),
  ("contentAttested", .required (.bool .anyBool)),
  ("sourceDigestMatches", .required (.bool .anyBool))]
def uploadAction : ActionSchemaEntry :=
  ⟨Set.make [serviceType], Set.make [documentType], Set.empty, contextType⟩
def serviceEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [("kind", .required .string)], none⟩
def documentEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("patient", .required .string), ("kind", .required .string)], none⟩
def schema : Schema :=
  ⟨Map.make [(serviceType, serviceEntry), (documentType, documentEntry)],
    Map.make [(upload, uploadAction)]⟩
def serviceData (kind : String) : EntityData :=
  { attrs := Map.make [("kind", .prim (.string kind))],
    ancestors := Set.empty, tags := Map.empty }
def documentData (patient kind : String) : EntityData :=
  { attrs := Map.make [("patient", .prim (.string patient)),
      ("kind", .prim (.string kind))],
    ancestors := Set.empty, tags := Map.empty }
def entities : Entities := Map.make [
  (hospital, serviceData "hospital"), (agent, serviceData "agent"),
  (dischargeA, documentData "patient-a" "discharge"),
  (dischargeB, documentData "patient-b" "discharge"),
  (medicationA, documentData "patient-a" "medication"),
  (upload, actionSchemaEntryToEntityData uploadAction)]

def broadUpload : Policy :=
  { id := "emr-upload", effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq upload),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := .lit (.bool true) }] }
def uploadProfile : EMRUpload :=
  { policyId := broadUpload.id, action := upload,
    principalKind := "hospital", documentKind := "discharge",
    purpose := "care-continuity" }
def boundedUpload : Policy := uploadProfile.policy
def legacyAgentUpload : Policy :=
  { broadUpload with id := "legacy-agent-upload" }

def identityControl : Veto :=
  (PatientBinding.control {
    policyId := "emr-patient-identity", actionScope := .actionScope (.eq upload),
    identifierVerifiedFact := "ihiVerified" })
def instructionControl : Veto :=
  uploadProfile.patientInstruction "patient-no-upload"
def evidenceControl : Veto :=
  (PayloadBinding.control {
    policyId := "unattested-document", actionScope := .actionScope (.eq upload) })
def incidentControl : Veto :=
  { policyId := "emr-upload-incident", actionScope := .actionScope (.eq upload),
    denyWhen := .lit (.bool true) }

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [.extend broadUpload, .extend legacyAgentUpload] }] }
  let identity ← base.extend "Identity" "Base" [identityControl.edit .introduce]
  let instruction ← identity.extend "PatientInstruction" "Base"
    [instructionControl.edit .introduce]
  let evidence ← instruction.extend "DeliveryEvidence" "Base"
    [evidenceControl.edit .introduce]
  let governed ← evidence.mix "Governed"
    ["Identity", "PatientInstruction", "DeliveryEvidence"]
    [uploadProfile.strengthen, .remove legacyAgentUpload.id]
  let incident ← governed.extend "Incident" "Governed"
    [incidentControl.edit .introduce]
  incident.extend "Recovered" "Incident" [incidentControl.edit .withdraw]
def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)


structure Facts where
  subjectPatient : String := "patient-a"
  purpose : String := "care-continuity"
  ihiVerified : Bool := true
  patientDeclinedUpload : Bool := false
  contentAttested : Bool := true
  sourceDigestMatches : Bool := true

def request (actor document : EntityUID) (facts : Facts := {}) : Request :=
  ⟨actor, upload, document, Map.make [
    ("subjectPatient", .prim (.string facts.subjectPatient)),
    ("purpose", .prim (.string facts.purpose)),
    ("ihiVerified", .prim (.bool facts.ihiVerified)),
    ("patientDeclinedUpload", .prim (.bool facts.patientDeclinedUpload)),
    ("contentAttested", .prim (.bool facts.contentAttested)),
    ("sourceDigestMatches", .prim (.bool facts.sourceDigestMatches))]⟩

def cases : List (String × String × Request × Decision) := [
  ("legacy-agent-risk", "Base", request agent dischargeA, .allow),
  ("governed-discharge", "Governed", request hospital dischargeA, .allow),
  ("other-patient", "Governed", request hospital dischargeB, .deny),
  ("ihi-unverified", "Governed", request hospital dischargeA
    { ihiVerified := false }, .deny),
  ("patient-declined", "Governed", request hospital dischargeA
    { patientDeclinedUpload := true }, .deny),
  ("document-unattested", "Governed", request hospital dischargeA
    { contentAttested := false }, .deny),
  ("source-swapped", "Governed", request hospital dischargeA
    { sourceDigestMatches := false }, .deny),
  ("wrong-purpose", "Governed", request hospital dischargeA
    { purpose := "marketing" }, .deny),
  ("wrong-document-class", "Governed", request hospital medicationA, .deny),
  ("agent-cannot-upload", "Governed", request agent dischargeA, .deny),
  ("incident-freezes-upload", "Incident", request hospital dischargeA, .deny),
  ("recovered-upload", "Recovered", request hospital dischargeA, .allow),
  ("recovered-still-honors-instruction", "Recovered", request hospital dischargeA
    { patientDeclinedUpload := true }, .deny)]

def casesConform
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AustralianEMRExample.model CedarPooSpec.AustralianEMRExample.schema :=
      CedarPooSpec.AustralianEMRExample.program) : Bool := cases.all fun (_, root, req, expected) =>
  match programContext.response root req entities with
  | .error _ => false
  | .ok answer =>
      answer.decision == expected && answer.erroringPolicies.isEmpty
theorem casesConformFully : casesConform = true := by native_decide
theorem legacyAgentRemoved :
    ((model.compile "Governed").toOption.get (by native_decide)).all
      (fun policy => policy.id != legacyAgentUpload.id) = true := by native_decide
theorem incidentChangesOnePolicy :
    ((model.compileRevision "Governed" "Incident").toOption.get
      (by native_decide)).changedPolicyIds = ["emr-upload-incident"] := by native_decide

end CedarPooSpec.AustralianEMRExample
