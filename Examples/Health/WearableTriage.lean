import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.Authorization.Compound
import CedarPooSpec.Governance.Veto
import Cedar.Validation.RequestEntityValidator

/-!
Remote monitoring observations may be analyzed by an AI service, but an alert
is released only after a clinician reviews it. The source devices, patients,
and institutions here are fictive. Trusted systems project consent, device
posture, model approval, and review facts into Cedar inputs.
-/

namespace CedarPooSpec.WearableTriageExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Governance

def serviceType : EntityType := ⟨"TriageService", []⟩
def clinicianType : EntityType := ⟨"Clinician", []⟩
def observationType : EntityType := ⟨"Observation", []⟩
def actionType : EntityType := ⟨"Action", []⟩

def triageService : EntityUID := ⟨serviceType, "ai-triage"⟩
def clinician : EntityUID := ⟨clinicianType, "cardiology-a"⟩
def vitalA : EntityUID := ⟨observationType, "vital-a"⟩
def vitalSuspect : EntityUID := ⟨observationType, "vital-suspect"⟩
def vitalWithdrawn : EntityUID := ⟨observationType, "vital-withdrawn"⟩
def vitalOtherSite : EntityUID := ⟨observationType, "vital-other-site"⟩
def laboratoryA : EntityUID := ⟨observationType, "laboratory-a"⟩
def analyze : EntityUID := ⟨actionType, "analyze"⟩
def release : EntityUID := ⟨actionType, "release-alert"⟩

def principalEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [("facility", .required .string)], none⟩
def observationEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("facility", .required .string),
    ("category", .required .string),
    ("source", .required .string),
    ("consentActive", .required (.bool .anyBool))], none⟩
def contextType : RecordType := Map.make [
  ("treatmentPurpose", .required (.bool .anyBool)),
  ("deviceTrusted", .required (.bool .anyBool)),
  ("modelApproved", .required (.bool .anyBool)),
  ("clinicianReviewed", .required (.bool .anyBool))]
def analyzeEntry : ActionSchemaEntry :=
  ⟨Set.make [serviceType], Set.make [observationType], Set.empty, contextType⟩
def releaseEntry : ActionSchemaEntry :=
  ⟨Set.make [clinicianType], Set.make [observationType], Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [(serviceType, principalEntry), (clinicianType, principalEntry),
    (observationType, observationEntry)],
    Map.make [(analyze, analyzeEntry), (release, releaseEntry)]⟩

def principalData : EntityData :=
  { attrs := Map.make [("facility", .prim (.string "a"))],
    ancestors := Set.empty, tags := Map.empty }
def observationData (facility category source : String) (consent : Bool) : EntityData :=
  { attrs := Map.make [
      ("facility", .prim (.string facility)),
      ("category", .prim (.string category)),
      ("source", .prim (.string source)),
      ("consentActive", .prim (.bool consent))],
    ancestors := Set.empty, tags := Map.empty }
def entities : Entities := Map.make [
  (triageService, principalData), (clinician, principalData),
  (vitalA, observationData "a" "vital-signs" "monitor-a" true),
  (vitalSuspect, observationData "a" "vital-signs" "monitor-q" true),
  (vitalWithdrawn, observationData "a" "vital-signs" "monitor-a" false),
  (vitalOtherSite, observationData "b" "vital-signs" "monitor-b" true),
  (laboratoryA, observationData "a" "laboratory" "monitor-a" true),
  (analyze, actionSchemaEntryToEntityData analyzeEntry),
  (release, actionSchemaEntryToEntityData releaseEntry)]

def contextFact (name : String) : Expr := .getAttr (.var .context) name
def resourceFact (name : String) : Expr := .getAttr (.var .resource) name
def principalFact (name : String) : Expr := .getAttr (.var .principal) name
def eq (left right : Expr) : Expr := .binaryApp .eq left right
def vitalSign : Expr := eq (resourceFact "category") (.lit (.string "vital-signs"))
def sameFacility : Expr := eq (principalFact "facility") (resourceFact "facility")
def treatment : Expr := contextFact "treatmentPurpose"

def policy (id : String) (effect : Effect) (action : Scope) (body : Expr) : Policy :=
  { id, effect,
    principalScope := .principalScope .any,
    actionScope := .actionScope action,
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body }] }

def analyzeBase : Policy :=
  policy "analyze-vitals" .permit (.eq analyze) (.and vitalSign treatment)
def releaseBase : Policy :=
  policy "release-alert" .permit (.eq release) (.and sameFacility treatment)
def consentControl : Veto :=
  { policyId := "consent-withdrawn", actionScope := .actionScope .any,
    denyWhen := .unaryApp .not (resourceFact "consentActive") }
def consentVeto : Policy := consentControl.policy
def deviceControl : Veto :=
  { policyId := "untrusted-monitor", actionScope := .actionScope .any,
    denyWhen := .unaryApp .not (contextFact "deviceTrusted") }
def deviceVeto : Policy := deviceControl.policy
def analyzeApproved : Policy :=
  { analyzeBase with condition := [
      { kind := .when,
        body := .and (.and vitalSign treatment) (contextFact "modelApproved") }] }
def releaseReviewed : Policy :=
  { releaseBase with condition := [
      { kind := .when,
        body := .and (.and sameFacility treatment) (contextFact "clinicianReviewed") }] }
def quarantineControl : Veto :=
  { policyId := "quarantine-monitor-q", actionScope := .actionScope .any,
    denyWhen := eq (resourceFact "source") (.lit (.string "monitor-q")) }
def quarantineVeto : Policy := quarantineControl.policy

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [.extend analyzeBase, .extend releaseBase] }] }
  let privacy ← base.extend "Privacy" "Base" [consentControl.edit .introduce]
  let device ← privacy.extend "DeviceSecurity" "Base" [deviceControl.edit .introduce]
  let clinical ← device.extend "ClinicalAI" "Base"
    [.overlay analyzeApproved, .overlay releaseReviewed]
  let integrated ← clinical.mix "Integrated"
    ["Privacy", "DeviceSecurity", "ClinicalAI"]
  let quarantined ← integrated.extend "Quarantined" "Integrated"
    [quarantineControl.edit .introduce]
  quarantined.extend "Recovered" "Quarantined" [quarantineControl.edit .withdraw]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)


structure Facts where
  treatmentPurpose : Bool := true
  deviceTrusted : Bool := true
  modelApproved : Bool := true
  clinicianReviewed : Bool := true

def requestContext (facts : Facts) : Map String Value := Map.make [
  ("treatmentPurpose", .prim (.bool facts.treatmentPurpose)),
  ("deviceTrusted", .prim (.bool facts.deviceTrusted)),
  ("modelApproved", .prim (.bool facts.modelApproved)),
  ("clinicianReviewed", .prim (.bool facts.clinicianReviewed))]
def checks (root : String) (observation : EntityUID) (facts : Facts) :
    List (String × Request) := [
  (root, ⟨triageService, analyze, observation, requestContext facts⟩),
  (root, ⟨clinician, release, observation, requestContext facts⟩)]
def authorizeFlow
     (root : String) (observation : EntityUID) (facts : Facts)
    (world : Entities := entities)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.WearableTriageExample.model CedarPooSpec.WearableTriageExample.schema :=
      CedarPooSpec.WearableTriageExample.program) : Bool :=
  match programContext.authorizeLayers (checks root observation facts) world with
  | .error _ => false
  | .ok receipts => CedarPooSpec.Authorization.Compound.layersAllowed receipts

def cases : List (String × String × EntityUID × Facts × Bool) := [
  ("legacy-withdrawn-consent", "Base", vitalWithdrawn, {}, true),
  ("integrated-vitals", "Integrated", vitalA, {}, true),
  ("withdrawn-consent", "Integrated", vitalWithdrawn, {}, false),
  ("untrusted-device", "Integrated", vitalA, { deviceTrusted := false }, false),
  ("unapproved-model", "Integrated", vitalA, { modelApproved := false }, false),
  ("no-clinician-review", "Integrated", vitalA, { clinicianReviewed := false }, false),
  ("wrong-purpose", "Integrated", vitalA, { treatmentPurpose := false }, false),
  ("other-facility", "Integrated", vitalOtherSite, {}, false),
  ("non-vital-observation", "Integrated", laboratoryA, {}, false),
  ("suspect-before-quarantine", "Integrated", vitalSuspect, {}, true),
  ("suspect-quarantined", "Quarantined", vitalSuspect, {}, false),
  ("other-monitor-during-quarantine", "Quarantined", vitalA, {}, true),
  ("suspect-after-recovery", "Recovered", vitalSuspect, {}, true)]

def casesExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.WearableTriageExample.model CedarPooSpec.WearableTriageExample.schema :=
      CedarPooSpec.WearableTriageExample.program) : Bool := cases.all fun (_, root, observation, facts, expected) =>
  (authorizeFlow (programContext := programContext)) root observation facts == expected
theorem casesExactFully : casesExact = true := by native_decide

def casesErrorFree
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.WearableTriageExample.model CedarPooSpec.WearableTriageExample.schema :=
      CedarPooSpec.WearableTriageExample.program) : Bool := cases.all fun (_, root, observation, facts, _) =>
  match programContext.authorizeLayers (checks root observation facts) entities with
  | .error _ => false
  | .ok receipts => receipts.all fun layer => layer.response.erroringPolicies.isEmpty
theorem casesErrorFreeFully : casesErrorFree = true := by native_decide

def rootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.WearableTriageExample.model CedarPooSpec.WearableTriageExample.schema :=
      CedarPooSpec.WearableTriageExample.program) : Bool :=
  ["Base", "Privacy", "DeviceSecurity", "ClinicalAI", "Integrated",
    "Quarantined", "Recovered"].all fun root =>
      (programContext.publish root).isOk
theorem rootsValidatedFully : rootsValidated = true := by native_decide

theorem quarantineChangesOnePolicy :
    ((model.compileRevision "Integrated" "Quarantined").toOption.get
      (by native_decide)).changedPolicyIds = ["quarantine-monitor-q"] := by native_decide
theorem recoveryChangesOnePolicy :
    ((model.compileRevision "Quarantined" "Recovered").toOption.get
      (by native_decide)).changedPolicyIds = ["quarantine-monitor-q"] := by native_decide
theorem recoveredPoliciesEqualIntegrated :
    (model.compile "Recovered" == model.compile "Integrated") = true := by native_decide

def consentRestored : Entities := Map.make (entities.toList.map fun (uid, data) =>
  if uid == vitalWithdrawn then
    (uid, observationData "a" "vital-signs" "monitor-a" true)
  else (uid, data))
theorem consentChangeWithoutPolicyEdit :
    authorizeFlow "Integrated" vitalWithdrawn {} = false ∧
    authorizeFlow "Integrated" vitalWithdrawn {} consentRestored = true := by
  native_decide

end CedarPooSpec.WearableTriageExample
