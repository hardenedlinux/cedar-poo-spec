import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Revision
import CedarPooSpec.PolicyJson
import CedarPooSpec.Authorization.Compound
import Cedar.Validation.RequestEntityValidator

/-!
A policy projection of Uptane Deployment Best Practices 2.1.0, section 6.3:
removing a tier-1 supplier requires both Image-repository delegation removal
and Director-repository assignment removal. A successor needs a new Image
delegation. Snapshot rollback records and cryptographic checks are inputs from
the host; this example does not implement the Uptane protocol or ECU verifier.
-/

namespace CedarPooSpec.SupplierTransitionExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Soundness CedarPooSpec.PolicyValidation LeanPoo.Proof

def supplierType : EntityType := ⟨"Supplier", []⟩
def directorType : EntityType := ⟨"DirectorService", []⟩
def primaryType : EntityType := ⟨"PrimaryECU", []⟩
def imageType : EntityType := ⟨"ImageTarget", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def oldSupplier : EntityUID := ⟨supplierType, "retired-tier-1"⟩
def newSupplier : EntityUID := ⟨supplierType, "replacement-tier-1"⟩
def director : EntityUID := ⟨directorType, "oem-director"⟩
def primary : EntityUID := ⟨primaryType, "vehicle-primary"⟩
def oldImage : EntityUID := ⟨imageType, "retired-image"⟩
def newImage : EntityUID := ⟨imageType, "replacement-image"⟩
def incompatibleImage : EntityUID := ⟨imageType, "incompatible-replacement"⟩
def publish : EntityUID := ⟨actionType, "publish-image"⟩
def assign : EntityUID := ⟨actionType, "assign-target"⟩
def report : EntityUID := ⟨actionType, "submit-manifest"⟩

def emptyEntry : EntitySchemaEntry := .standard ⟨Set.empty, Map.empty, none⟩
def imageEntry : EntitySchemaEntry := .standard ⟨Set.empty, Map.make [
  ("retiredSupplier", .required (.bool .anyBool)),
  ("compatible", .required (.bool .anyBool))], none⟩
def contextType : RecordType := Map.make [
  ("delegationValid", .required (.bool .anyBool)),
  ("metadataAuthenticated", .required (.bool .anyBool)),
  ("snapshotRetainsRevocation", .required (.bool .anyBool)),
  ("manifestSignatureValid", .required (.bool .anyBool))]
def actionEntry (principal : EntityType) : ActionSchemaEntry :=
  ⟨Set.make [principal], Set.make [imageType], Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [(supplierType, emptyEntry), (directorType, emptyEntry),
    (primaryType, emptyEntry), (imageType, imageEntry)],
    Map.make [(publish, actionEntry supplierType),
      (assign, actionEntry directorType), (report, actionEntry primaryType)]⟩

def emptyData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }
def imageData (retired compatible : Bool) : EntityData :=
  { attrs := Map.make [
      ("retiredSupplier", .prim (.bool retired)),
      ("compatible", .prim (.bool compatible))],
    ancestors := Set.empty, tags := Map.empty }
def entities : Entities := Map.make [
  (oldSupplier, emptyData), (newSupplier, emptyData),
  (director, emptyData), (primary, emptyData),
  (oldImage, imageData true true),
  (newImage, imageData false true),
  (incompatibleImage, imageData false false),
  (publish, actionSchemaEntryToEntityData (actionEntry supplierType)),
  (assign, actionSchemaEntryToEntityData (actionEntry directorType)),
  (report, actionSchemaEntryToEntityData (actionEntry primaryType))]

def ctx (name : String) : Expr := .getAttr (.var .context) name
def imageFact (name : String) : Expr := .getAttr (.var .resource) name
def notRetired : Expr := .unaryApp .not (imageFact "retiredSupplier")
def policy (id : String) (principal action : EntityUID) (body : Expr) : Policy :=
  { id, effect := .permit,
    principalScope := .principalScope (.eq principal),
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body }] }

def oldPublish : Policy := policy "old-image-delegation" oldSupplier publish
  (.and (ctx "delegationValid")
    (.and (ctx "metadataAuthenticated")
      (.and (imageFact "retiredSupplier") (imageFact "compatible"))))
def oldAssignment : Policy := policy "old-director-assignment" director assign
  (.and (ctx "metadataAuthenticated")
    (.and (imageFact "retiredSupplier") (imageFact "compatible")))
def manifestIntake : Policy := policy "primary-version-manifest" primary report
  (ctx "manifestSignatureValid")
def newPublish : Policy := policy "new-image-delegation" newSupplier publish
  (.and (ctx "delegationValid")
    (.and (ctx "metadataAuthenticated")
      (.and notRetired (imageFact "compatible"))))
def newAssignment : Policy := policy "new-director-assignment" director assign
  (.and (ctx "snapshotRetainsRevocation")
    (.and (ctx "metadataAuthenticated")
      (.and notRetired (imageFact "compatible"))))

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [
        .extend oldPublish, .extend oldAssignment, .extend manifestIntake] }] }
  let image ← base.extend "ImageRemoval" "Base" [.remove oldPublish.id]
  let director ← image.extend "DirectorRemoval" "Base" [.remove oldAssignment.id]
  let retired ← director.mix "Retired" ["ImageRemoval", "DirectorRemoval"]
  retired.extend "Replacement" "Retired" [.extend newPublish, .extend newAssignment]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)


structure Facts where
  delegationValid : Bool := true
  metadataAuthenticated : Bool := true
  snapshotRetainsRevocation : Bool := true
  manifestSignatureValid : Bool := true

def context (facts : Facts) : Map String Value := Map.make [
  ("delegationValid", .prim (.bool facts.delegationValid)),
  ("metadataAuthenticated", .prim (.bool facts.metadataAuthenticated)),
  ("snapshotRetainsRevocation", .prim (.bool facts.snapshotRetainsRevocation)),
  ("manifestSignatureValid", .prim (.bool facts.manifestSignatureValid))]
def updateChecks (root : String) (supplier target : EntityUID) (facts : Facts) :
    List (String × Request) := [
  (root, ⟨supplier, publish, target, context facts⟩),
  (root, ⟨director, assign, target, context facts⟩)]
def manifestRequest (target : EntityUID) (facts : Facts) : Request :=
  ⟨primary, report, target, context facts⟩
def allowed
     (checks : List (String × Request))
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SupplierTransitionExample.model CedarPooSpec.SupplierTransitionExample.schema :=
      CedarPooSpec.SupplierTransitionExample.program) : Bool :=
  match programContext.authorizeLayers checks entities with
  | .error _ => false
  | .ok receipts => CedarPooSpec.Authorization.Compound.layersAllowed receipts
def authorizeUpdate
     (root : String) (supplier target : EntityUID) (facts : Facts)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SupplierTransitionExample.model CedarPooSpec.SupplierTransitionExample.schema :=
      CedarPooSpec.SupplierTransitionExample.program) : Bool :=
  (allowed (programContext := programContext)) (updateChecks root supplier target facts)

-- Each layer is asserted separately: a one-sided removal must not appear
-- complete merely because the compound operation already denies.
def updateCases : List (String × String × EntityUID × EntityUID × Facts × Bool × Bool) := [
  ("old-before-removal", "Base", oldSupplier, oldImage, {}, true, true),
  ("replacement-not-yet-delegated", "Base", newSupplier, newImage, {}, false, false),
  ("image-only-removal", "ImageRemoval", oldSupplier, oldImage, {}, false, true),
  ("director-only-removal", "DirectorRemoval", oldSupplier, oldImage, {}, true, false),
  ("both-repositories-retired", "Retired", oldSupplier, oldImage, {}, false, false),
  ("old-image-remains-retired", "Replacement", oldSupplier, oldImage, {}, false, false),
  ("replacement-authorized", "Replacement", newSupplier, newImage, {}, true, true),
  ("missing-new-delegation", "Replacement", newSupplier, newImage,
    { delegationValid := false }, false, true),
  ("missing-snapshot-revocation", "Replacement", newSupplier, newImage,
    { snapshotRetainsRevocation := false }, true, false),
  ("unverified-metadata", "Replacement", newSupplier, newImage,
    { metadataAuthenticated := false }, false, false),
  ("incompatible-replacement", "Replacement", newSupplier, incompatibleImage,
    {}, false, false)]
def manifestCases : List (String × String × EntityUID × Facts × Bool) := [
  ("manifest-before-removal", "Base", oldImage, {}, true),
  ("manifest-after-retirement", "Retired", oldImage, {}, true),
  ("manifest-after-replacement", "Replacement", newImage, {}, true),
  ("unsigned-manifest", "Replacement", newImage,
    { manifestSignatureValid := false }, false)]

def casesExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SupplierTransitionExample.model CedarPooSpec.SupplierTransitionExample.schema :=
      CedarPooSpec.SupplierTransitionExample.program) : Bool :=
  updateCases.all (fun (_, root, supplier, target, facts, imageExpected, directorExpected) =>
    let checks := updateChecks root supplier target facts
    (allowed (programContext := programContext)) [checks[0]!] == imageExpected &&
    (allowed (programContext := programContext)) [checks[1]!] == directorExpected &&
    (authorizeUpdate (programContext := programContext)) root supplier target facts == (imageExpected && directorExpected)) &&
  manifestCases.all (fun (_, root, target, facts, expected) =>
    (allowed (programContext := programContext)) [(root, manifestRequest target facts)] == expected)
theorem casesExactFully : casesExact = true := by native_decide

def rootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SupplierTransitionExample.model CedarPooSpec.SupplierTransitionExample.schema :=
      CedarPooSpec.SupplierTransitionExample.program) : Bool :=
  ["Base", "ImageRemoval", "DirectorRemoval", "Retired", "Replacement"].all fun root =>
    (programContext.publish root).isOk
theorem rootsValidatedFully : rootsValidated = true := by native_decide

def retirement : Revision :=
  (model.compileRevision "Base" "Retired").toOption.get (by native_decide)
theorem retirementDelta :
    retirement.changedPolicyIds.length = 2 ∧
    retirement.changedPolicyIds.contains oldPublish.id ∧
    retirement.changedPolicyIds.contains oldAssignment.id ∧
    retirement.freshPolicies = [] := by native_decide

def replacement : Revision :=
  (model.compileRevision "Retired" "Replacement").toOption.get (by native_decide)
theorem replacementDelta :
    replacement.changedPolicyIds.length = 2 ∧
    replacement.changedPolicyIds.contains newPublish.id ∧
    replacement.changedPolicyIds.contains newAssignment.id ∧
    replacement.freshPolicies.length = 2 := by native_decide

def manifestAtRetirement : Request := manifestRequest oldImage {}
def retirementBefore : AuthorizationSnapshot :=
  retirement.beforeSnapshot schema manifestAtRetirement entities
theorem retirementBaseline : Certificate retirementBefore.proofObject :=
  retirementBefore.certificateOfChecks (by native_decide)
theorem retirementCertificate :
    Certificate (retirement.afterSnapshot schema manifestAtRetirement entities).proofObject :=
  retirement.authorizationCertificate schema manifestAtRetirement entities
    (by simpa [retirementBefore] using retirementBaseline)
    (by intro policy member; simp [retirementDelta.2.2.2] at member)
example : Cedar.Thm.AllEvaluateToBool retirement.afterPolicies
    manifestAtRetirement entities :=
  certifiedAuthorizationSound
    (retirement.afterSnapshot schema manifestAtRetirement entities)
    retirementCertificate

end CedarPooSpec.SupplierTransitionExample
