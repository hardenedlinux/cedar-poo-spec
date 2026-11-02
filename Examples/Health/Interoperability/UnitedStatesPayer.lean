import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.SchemaJson
import CedarPooSpec.Vertical.Health.Region.UnitedStates

/-!
Synthetic impacted-payer exchange with separate Provider Access and
Payer-to-Payer paths. The Host supplies authenticated patient and payer
facts, USCDI/US Core/FHIR validation, treatment attribution, and consent.
-/

namespace CedarPooSpec.UnitedStatesPayerExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Governance CedarPooSpec.Vertical.Health.ClinicalExchange
open CedarPooSpec.Vertical.Health.Region.UnitedStates

def actorType : EntityType := ⟨"PayerExchangeActor", []⟩
def recordType : EntityType := ⟨"PayerClinicalRecord", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def provider : EntityUID := ⟨actorType, "attributed-provider"⟩
def receivingPayer : EntityUID := ⟨actorType, "receiving-payer"⟩
def clinicalA : EntityUID := ⟨recordType, "clinical-a"⟩
def clinicalB : EntityUID := ⟨recordType, "clinical-b"⟩
def shareWithProvider : EntityUID := ⟨actionType, "provider-access"⟩
def transferToPayer : EntityUID := ⟨actionType, "payer-to-payer"⟩

def contextType : RecordType := Map.make [
  ("subjectPatient", .required .string),
  ("identityVerified", .required (.bool .anyBool)),
  ("treatmentRelationship", .required (.bool .anyBool)),
  ("patientOptOut", .required (.bool .anyBool)),
  ("patientOptIn", .required (.bool .anyBool)),
  ("contentAttested", .required (.bool .anyBool)),
  ("sourceDigestMatches", .required (.bool .anyBool))]
def shareAction : ActionSchemaEntry :=
  ⟨Set.make [actorType], Set.make [recordType], Set.empty, contextType⟩
def actorEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [("kind", .required .string)], none⟩
def recordEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("kind", .required .string), ("patient", .required .string)], none⟩
def schema : Schema :=
  ⟨Map.make [(actorType, actorEntry), (recordType, recordEntry)],
    Map.make [(shareWithProvider, shareAction),
      (transferToPayer, shareAction)]⟩
def actorData (kind : String) : EntityData :=
  { attrs := Map.make [("kind", .prim (.string kind))],
    ancestors := Set.empty, tags := Map.empty }
def recordData (patient : String) : EntityData :=
  { attrs := Map.make [("kind", .prim (.string "clinical")),
      ("patient", .prim (.string patient))],
    ancestors := Set.empty, tags := Map.empty }
def entities : Entities := Map.make [
  (provider, actorData "provider"), (receivingPayer, actorData "payer"),
  (clinicalA, recordData "patient-a"),
  (clinicalB, recordData "patient-b"),
  (shareWithProvider, actionSchemaEntryToEntityData shareAction),
  (transferToPayer, actionSchemaEntryToEntityData shareAction)]

def broadPermit (id : String) (action : EntityUID) : Policy :=
  { id, effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := .lit (.bool true) }] }
def providerProfile : PayerExchange :=
  { policyId := "provider-access-grant", action := shareWithProvider,
    path := .providerAccess, principalKind := "provider",
    resourceKind := "clinical" }
def payerProfile : PayerExchange :=
  { policyId := "payer-transfer-grant", action := transferToPayer,
    path := .payerToPayer, principalKind := "payer",
    resourceKind := "clinical" }

def identityControl : Veto :=
  (PatientBinding.control {
    policyId := "payer-patient-binding",
    actionScope := .actionInAny [shareWithProvider, transferToPayer],
    identifierVerifiedFact := "identityVerified" })
def evidenceControl : Veto :=
  (PayloadBinding.control {
    policyId := "payer-payload-binding",
    actionScope := .actionInAny [shareWithProvider, transferToPayer] })
def incidentControl : Veto :=
  { policyId := "payer-exchange-incident",
    actionScope := .actionInAny [shareWithProvider, transferToPayer],
    denyWhen := .lit (.bool true) }

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [
      .extend (broadPermit providerProfile.policyId shareWithProvider),
      .extend (broadPermit payerProfile.policyId transferToPayer)] }] }
  let identity ← base.extend "Identity" "Base" [identityControl.edit .introduce]
  let choice ← identity.extend "PatientChoice" "Base" [
    (providerProfile.patientChoice "provider-opt-out").edit .introduce,
    (payerProfile.patientChoice "payer-opt-in").edit .introduce]
  let evidence ← choice.extend "DeliveryEvidence" "Base"
    [evidenceControl.edit .introduce]
  let governed ← evidence.mix "Governed"
    ["Identity", "PatientChoice", "DeliveryEvidence"]
    [providerProfile.strengthen, payerProfile.strengthen]
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
  identityVerified : Bool := true
  treatmentRelationship : Bool := true
  patientOptOut : Bool := false
  patientOptIn : Bool := true
  contentAttested : Bool := true
  sourceDigestMatches : Bool := true

def request (actor action resource : EntityUID) (facts : Facts := {}) : Request :=
  ⟨actor, action, resource, Map.make [
    ("subjectPatient", .prim (.string facts.subjectPatient)),
    ("identityVerified", .prim (.bool facts.identityVerified)),
    ("treatmentRelationship", .prim (.bool facts.treatmentRelationship)),
    ("patientOptOut", .prim (.bool facts.patientOptOut)),
    ("patientOptIn", .prim (.bool facts.patientOptIn)),
    ("contentAttested", .prim (.bool facts.contentAttested)),
    ("sourceDigestMatches", .prim (.bool facts.sourceDigestMatches))]⟩

def cases : List (String × String × Request × Decision) := [
  ("base-unattributed-provider", "Base", request provider shareWithProvider
    clinicalA { treatmentRelationship := false }, .allow),
  ("provider-attributed", "Governed", request provider shareWithProvider
    clinicalA, .allow),
  ("provider-no-relationship", "Governed", request provider shareWithProvider
    clinicalA { treatmentRelationship := false }, .deny),
  ("provider-opted-out", "Governed", request provider shareWithProvider
    clinicalA { patientOptOut := true }, .deny),
  ("provider-wrong-patient", "Governed", request provider shareWithProvider
    clinicalB, .deny),
  ("provider-unverified-identity", "Governed", request provider
    shareWithProvider clinicalA { identityVerified := false }, .deny),
  ("provider-unattested-content", "Governed", request provider
    shareWithProvider clinicalA { contentAttested := false }, .deny),
  ("payer-opted-in", "Governed", request receivingPayer transferToPayer
    clinicalA, .allow),
  ("payer-not-opted-in", "Governed", request receivingPayer transferToPayer
    clinicalA { patientOptIn := false }, .deny),
  ("payer-wrong-patient", "Governed", request receivingPayer transferToPayer
    clinicalB, .deny),
  ("payer-swapped-source", "Governed", request receivingPayer transferToPayer
    clinicalA { sourceDigestMatches := false }, .deny),
  ("provider-cannot-transfer", "Governed", request provider transferToPayer
    clinicalA, .deny),
  ("incident-freezes-provider", "Incident", request provider
    shareWithProvider clinicalA, .deny),
  ("incident-freezes-payer", "Incident", request receivingPayer
    transferToPayer clinicalA, .deny),
  ("recovered-provider", "Recovered", request provider shareWithProvider
    clinicalA, .allow),
  ("recovered-keeps-opt-in", "Recovered", request receivingPayer
    transferToPayer clinicalA { patientOptIn := false }, .deny)]

def casesConform
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.UnitedStatesPayerExample.model CedarPooSpec.UnitedStatesPayerExample.schema :=
      CedarPooSpec.UnitedStatesPayerExample.program) : Bool := cases.all fun (_, root, req, expected) =>
  match programContext.response root req entities with
  | .error _ => false
  | .ok answer =>
      answer.decision == expected && answer.erroringPolicies.isEmpty
theorem casesConformFully : casesConform = true := by native_decide
theorem incidentChangesOnePolicy :
    ((model.compileRevision "Governed" "Incident").toOption.get
      (by native_decide)).changedPolicyIds = ["payer-exchange-incident"] := by
  native_decide

end CedarPooSpec.UnitedStatesPayerExample
