import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Revision
import CedarPooSpec.Soundness
import CedarPooSpec.Vertical.Health.EmergencyAccess

/-!
Clinical record access derived from published Careweb and French DMP
workflows and HL7 FHIR security-label guidance. The entity names are fictive.
Request context is projected by a trusted application; break-glass grant,
authentication, device posture, and audit logging are external responsibilities.
-/

namespace CedarPooSpec.ClinicalBreakGlassExample

open Cedar.Spec Cedar.Validation Cedar.Data
open CedarPooSpec.PolicyModules CedarPooSpec.Soundness
open CedarPooSpec.Vertical.Health
open LeanPoo.Proof

def clinicianType : EntityType := ⟨"Clinician", []⟩
def recordType : EntityType := ⟨"PatientRecord", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def readAction : EntityUID := ⟨actionType, "read"⟩
def emergencyControl : EmergencyAccess :=
  { policyId := "break-glass", action := readAction }

def clinicianEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [("facility", .required .string)], none⟩
def recordEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("facility", .required .string),
    ("patient", .required .string),
    ("restricted", .required (.bool .anyBool))], none⟩
def contextType : RecordType := Map.make [
  ("deviceTrusted", .required (.bool .anyBool)),
  ("strongAuth", .required (.bool .anyBool)),
  ("breakGlassGranted", .required (.bool .anyBool)),
  ("sessionActive", .required (.bool .anyBool)),
  ("patientUnableToConsent", .required (.bool .anyBool)),
  ("treatmentPurpose", .required (.bool .anyBool)),
  ("sessionPatient", .required .string)]
def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [clinicianType], Set.make [recordType], Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [(clinicianType, clinicianEntry), (recordType, recordEntry)],
   Map.make [(readAction, actionEntry)]⟩

def doctor : EntityUID := ⟨clinicianType, "doctor-a"⟩
def routineRecord : EntityUID := ⟨recordType, "routine-a"⟩
def restrictedRecord : EntityUID := ⟨recordType, "restricted-a"⟩
def remoteRecord : EntityUID := ⟨recordType, "remote-b"⟩

def recordData (facility patient : String) (restricted : Bool) : EntityData :=
  { attrs := Map.make [
      ("facility", .prim (.string facility)),
      ("patient", .prim (.string patient)),
      ("restricted", .prim (.bool restricted))],
    ancestors := Set.empty, tags := Map.empty }
def entities : Entities := Map.make [
  (doctor, { attrs := Map.make [("facility", .prim (.string "a"))],
             ancestors := Set.empty, tags := Map.empty }),
  (routineRecord, recordData "a" "patient-a" false),
  (restrictedRecord, recordData "a" "patient-r" true),
  (remoteRecord, recordData "b" "patient-b" true),
  (readAction, actionSchemaEntryToEntityData actionEntry)]

def contextFact (name : String) : Expr := .getAttr (.var .context) name
def principalFacility : Expr := .getAttr (.var .principal) "facility"
def resourceFact (name : String) : Expr := .getAttr (.var .resource) name
def sameFacility : Expr := .binaryApp .eq principalFacility (resourceFact "facility")
def trusted : Expr := contextFact "deviceTrusted"
def stronglyAuthenticated : Expr := contextFact "strongAuth"
def restricted : Expr := resourceFact "restricted"
def breakGlassValid : Expr := emergencyControl.valid

def readPolicy (id : String) (effect : Effect) (body : Expr) : Policy :=
  { id := id, effect := effect,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq readAction),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := body }] }

def routinePermit : Policy :=
  readPolicy "routine-read" .permit (.and sameFacility trusted)
def legacyPermit : Policy :=
  readPolicy "legacy-broad-read" .permit (.lit (.bool true))
def privacyForbid : Policy :=
  readPolicy "restricted-record" .forbid
    (.and restricted (.unaryApp .not breakGlassValid))
def deviceForbid : Policy :=
  readPolicy "untrusted-device-or-identity" .forbid
    (.or (.unaryApp .not trusted) (.unaryApp .not stronglyAuthenticated))
def provisionalEmergencyPermit : Policy := emergencyControl.provisional
def boundedEmergencyPermit : Policy := emergencyControl.bounded

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [.extend routinePermit, .extend legacyPermit] }] }
  let privacy ← base.extend "Privacy" "Base" [.extend privacyForbid]
  let security ← privacy.extend "Security" "Base" [.extend deviceForbid]
  let emergency ← security.extend "Emergency" "Base" [emergencyControl.introduce]
  emergency.mix "Integrated" ["Privacy", "Security", "Emergency"]
    [emergencyControl.strengthen, .remove legacyPermit.id]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

def compilation : Compilation :=
  (model.compileWithTrace "Integrated").toOption.get (by native_decide)
def finalPolicies : Policies := compilation.policies.map CompiledPolicy.policy
def provenance : List CompiledPolicy := compilation.policies

structure AccessContext where
  deviceTrusted : Bool := true
  strongAuth : Bool := true
  breakGlassGranted : Bool := false
  sessionActive : Bool := false
  patientUnableToConsent : Bool := false
  treatmentPurpose : Bool := false
  sessionPatient : String := ""

def request (record : EntityUID) (facts : AccessContext) : Request :=
  ⟨doctor, readAction, record, Map.make [
    ("deviceTrusted", .prim (.bool facts.deviceTrusted)),
    ("strongAuth", .prim (.bool facts.strongAuth)),
    ("breakGlassGranted", .prim (.bool facts.breakGlassGranted)),
    ("sessionActive", .prim (.bool facts.sessionActive)),
    ("patientUnableToConsent", .prim (.bool facts.patientUnableToConsent)),
    ("treatmentPurpose", .prim (.bool facts.treatmentPurpose)),
    ("sessionPatient", .prim (.string facts.sessionPatient))]⟩

def breakGlass (patient : String) : AccessContext :=
  { breakGlassGranted := true, sessionActive := true,
    patientUnableToConsent := true, treatmentPurpose := true,
    sessionPatient := patient }

def cases : List (String × Request × Decision) := [
  ("routine-care", request routineRecord {}, .allow),
  ("cross-site-without-break-glass", request remoteRecord {}, .deny),
  ("patient-preference", request restrictedRecord {}, .deny),
  ("expired-session", request restrictedRecord
    { (breakGlass "patient-r") with sessionActive := false }, .deny),
  ("wrong-patient", request restrictedRecord (breakGlass "patient-a"), .deny),
  ("cross-site-break-glass", request remoteRecord (breakGlass "patient-b"), .allow),
  ("other-patient", request remoteRecord (breakGlass "patient-a"), .deny),
  ("inactive-session", request remoteRecord
    { (breakGlass "patient-b") with sessionActive := false }, .deny),
  ("patient-can-consent", request remoteRecord
    { (breakGlass "patient-b") with patientUnableToConsent := false }, .deny),
  ("non-treatment-purpose", request remoteRecord
    { (breakGlass "patient-b") with treatmentPurpose := false }, .deny),
  ("untrusted-device", request remoteRecord
    { (breakGlass "patient-b") with deviceTrusted := false }, .deny),
  ("weak-authentication", request remoteRecord
    { (breakGlass "patient-b") with strongAuth := false }, .deny)]

-- Patient preference is entity data, so changing it does not rewrite the
-- clinical, privacy, emergency, or device policy modules.
def unrestrictedEntities : Entities :=
  Map.make (entities.toList.map fun (uid, data) =>
    if uid == restrictedRecord then
      (uid, recordData "a" "patient-r" false)
    else (uid, data))
def preferenceChangeConforms : Bool :=
  (validateEntities schema unrestrictedEntities).isOk &&
  (isAuthorized (request restrictedRecord {}) entities finalPolicies).decision == .deny &&
  (isAuthorized (request restrictedRecord {}) unrestrictedEntities finalPolicies).decision == .allow
theorem preferenceChangeConformsFully : preferenceChangeConforms = true := by
  native_decide

def scenarioConforms : Bool :=
  (validate finalPolicies schema).isOk &&
  cases.all fun (_, req, expected) =>
    let response := isAuthorized req entities finalPolicies
    response.decision == expected && response.erroringPolicies.isEmpty
theorem scenarioConformsFully : scenarioConforms = true := by native_decide

theorem caseNamesUnique : (cases.map (fun (name, _, _) => name)).Nodup := by
  native_decide

-- The branch carrying an emergency permit still inherits the broad legacy
-- permit. Only the integrated root retires that independent authorization.
def preIntegrationRisk : Bool :=
  match model.compile "Emergency" with
  | .error _ => false
  | .ok policies =>
    (validate policies schema).isOk &&
    (isAuthorized (request remoteRecord {})
      entities policies).decision == .allow &&
    (isAuthorized (request remoteRecord {})
      entities finalPolicies).decision == .deny
theorem preIntegrationRiskDetected : preIntegrationRisk = true := by native_decide

def provenanceConforms : Bool :=
  (LeanPoo.C4.linearize model.graph "Integrated").toOption ==
    some ["Integrated", "Privacy", "Security", "Emergency", "Base"] &&
  provenance.map (fun p => (p.policy.id, p.introducedBy, p.lastEditedBy)) == [
    ("routine-read", "Base", "Base"),
    ("break-glass", "Emergency", "Integrated"),
    ("untrusted-device-or-identity", "Security", "Security"),
    ("restricted-record", "Privacy", "Privacy")]
theorem provenanceConformsFully : provenanceConforms = true := by native_decide

def removalRecorded : Bool :=
  compilation.applied.length == 7 &&
  (match compilation.applied.getLast? with
   | some { moduleName := "Integrated", edit := .remove "legacy-broad-read" } => true
   | _ => false)
theorem removalRecordedFully : removalRecorded = true := by native_decide

def preferenceRevision : Patch AuthorizationKey AuthorizationValue :=
  Patch.set .entities unrestrictedEntities
def preferenceRevisionFootprint : Bool :=
  (match changedDependencies entitiesObligation preferenceRevision with
   | [.entities] => true
   | _ => false) &&
  (changedDependencies policiesObligation preferenceRevision).isEmpty &&
  (changedDependencies schemaObligation preferenceRevision).isEmpty &&
  (changedDependencies requestObligation preferenceRevision).isEmpty
theorem preferenceRevisionFootprintExact : preferenceRevisionFootprint = true := by
  native_decide

def emergencyRequest : Request :=
  request remoteRecord (breakGlass "patient-b")
def snapshot : AuthorizationSnapshot :=
  ⟨finalPolicies, schema, emergencyRequest, entities⟩
private theorem okOfIsOk {ε : Type} (result : Except ε Unit)
    (h : result.isOk = true) : result = .ok () := by
  cases result with
  | ok value => cases value; rfl
  | error _ => cases h
theorem certificate : Certificate snapshot.proofObject :=
  snapshot.certificateOfChecks (by native_decide)
example : Cedar.Thm.AllEvaluateToBool snapshot.policies
    snapshot.request snapshot.entities :=
  certifiedAuthorizationSound snapshot certificate

-- Privacy's patient restriction survives integration unchanged. Emergency and
-- device policies are the only new bodies needing Cedar validation.
def privacyRevision : Revision :=
  (model.compileRevision "Privacy" "Integrated").toOption.get (by native_decide)

theorem privacyRevisionBodies :
    privacyRevision.freshPolicies = [boundedEmergencyPermit, deviceForbid] ∧
    privacyRevision.afterPolicies.length - privacyRevision.freshPolicies.length = 2 := by
  native_decide

theorem privacyRevisionReused :
    (privacyRevision.beforePolicies.filter fun policy =>
      decide (policy ∈ privacyRevision.afterPolicies)) =
        [routinePermit, privacyForbid] := by
  native_decide

def privacySnapshot : AuthorizationSnapshot :=
  privacyRevision.beforeSnapshot schema emergencyRequest entities

theorem privacyCertificate : Certificate privacySnapshot.proofObject :=
  privacySnapshot.certificateOfChecks (by native_decide)

theorem freshClinicalValid :
    ∀ policy ∈ privacyRevision.freshPolicies,
      PolicyValidation.check policy schema = .ok () := by
  intro policy member
  rw [privacyRevisionBodies.1] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · subst policy
    exact okOfIsOk _ (by native_decide)
  · subst policy
    exact okOfIsOk _ (by native_decide)

theorem freshClinicalCertificates :
    ∀ policy ∈ privacyRevision.freshPolicies,
      Certificate (PolicyValidation.Snapshot.mk policy schema).proofObject := by
  intro policy member
  exact (PolicyValidation.Snapshot.mk policy schema).certificate
    (freshClinicalValid policy member)

theorem integratedCertificateFromPrivacy :
    Certificate
      (privacyRevision.afterSnapshot schema emergencyRequest entities).proofObject :=
  privacyRevision.authorizationCertificate schema emergencyRequest entities
    (by simpa [privacySnapshot] using privacyCertificate)
    freshClinicalCertificates

example : Cedar.Thm.AllEvaluateToBool privacyRevision.afterPolicies
    emergencyRequest entities :=
  certifiedAuthorizationSound
    (privacyRevision.afterSnapshot schema emergencyRequest entities)
    integratedCertificateFromPrivacy

end CedarPooSpec.ClinicalBreakGlassExample
