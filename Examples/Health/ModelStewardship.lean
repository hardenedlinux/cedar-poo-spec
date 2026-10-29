import CedarPooSpec.Functional.Compilation
import CedarPooSpec.Data.Lineage
import CedarPooSpec.Data.LineageUse
import CedarPooSpec.Governance.ScopedApproval
import CedarPooSpec.PolicyJson

/-!
Synthetic medical model lifecycle inspired by publicly announced healthcare AI
collaborations. It is not a description of any provider's deployed system.
The Host authenticates approvals, de-identification, lineage, review, and the
actual training, publication, and inference effects.
-/

namespace CedarPooSpec.ModelStewardshipExample

open Cedar.Spec Cedar.Data CedarPooSpec.PolicyModules
open CedarPooSpec.Data CedarPooSpec.Data.Lineage
open CedarPooSpec.Governance

def actorType : EntityType := ⟨"Actor", []⟩
def artifactType : EntityType := ⟨"Artifact", []⟩
def actionType : EntityType := ⟨"Action", []⟩

def trainer : EntityUID := ⟨actorType, "model-trainer"⟩
def publisher : EntityUID := ⟨actorType, "model-publisher"⟩
def clinician : EntityUID := ⟨actorType, "clinician"⟩
def studyReviewer : EntityUID := ⟨actorType, "study-reviewer"⟩
def releaseReviewer : EntityUID := ⟨actorType, "release-reviewer"⟩
def train : EntityUID := ⟨actionType, "train"⟩
def publish : EntityUID := ⟨actionType, "publish"⟩
def infer : EntityUID := ⟨actionType, "infer"⟩

def jointDataset : EntityUID := ⟨artifactType, "joint-dataset"⟩
def jointRun : EntityUID := ⟨artifactType, "joint-training-run"⟩
def jointModel : EntityUID := ⟨artifactType, "joint-model-v1"⟩
def jointEndpoint : EntityUID := ⟨artifactType, "joint-endpoint"⟩
def independentModel : EntityUID := ⟨artifactType, "hospital-a-model-v1"⟩
def independentEndpoint : EntityUID := ⟨artifactType, "hospital-a-endpoint"⟩

def catalog : Catalog := ⟨[
  ⟨"hospital-a-record", .source, []⟩,
  ⟨"hospital-b-record", .source, []⟩,
  ⟨"hospital-a-dataset", .fragment, ["hospital-a-record"]⟩,
  ⟨"hospital-b-dataset", .fragment, ["hospital-b-record"]⟩,
  ⟨"joint-dataset", .other "training-dataset",
    ["hospital-a-dataset", "hospital-b-dataset"]⟩,
  ⟨"joint-training-run", .other "training-run", ["joint-dataset"]⟩,
  ⟨"joint-model-v1", .other "model-checkpoint", ["joint-training-run"]⟩,
  ⟨"joint-endpoint", .other "deployment", ["joint-model-v1"]⟩,
  ⟨"joint-inference", .result, ["joint-endpoint"]⟩,
  ⟨"hospital-a-training-run", .other "training-run", ["hospital-a-dataset"]⟩,
  ⟨"hospital-a-model-v1", .other "model-checkpoint", ["hospital-a-training-run"]⟩,
  ⟨"hospital-a-endpoint", .other "deployment", ["hospital-a-model-v1"]⟩]⟩

def entity (attrs : List (String × Value)) : EntityData :=
  { attrs := Map.make attrs, ancestors := Set.empty, tags := Map.empty }

def artifactData (id kind revision : String) : EntityData :=
  entity [("artifactId", .prim (.string id)),
    ("kind", .prim (.string kind)),
    ("lineageRevision", .prim (.string revision))]

def entities (revision : String) : Entities := Map.make [
  (trainer, entity [("kind", .prim (.string "trainer"))]),
  (publisher, entity [("kind", .prim (.string "publisher"))]),
  (clinician, entity [("kind", .prim (.string "clinician"))]),
  (jointDataset, artifactData "joint-dataset" "dataset" revision),
  (jointRun, artifactData "joint-training-run" "run" revision),
  (jointModel, artifactData "joint-model-v1" "model" revision),
  (jointEndpoint, artifactData "joint-endpoint" "endpoint" revision),
  (independentModel, artifactData "hospital-a-model-v1" "model" revision),
  (independentEndpoint, artifactData "hospital-a-endpoint" "endpoint" revision)]

private def attr (source : Var) (name : String) : Expr :=
  .getAttr (.var source) name
private def eq (left right : Expr) : Expr := .binaryApp .eq left right
private def string (value : String) : Expr := .lit (.string value)
private def all (conditions : List Expr) : Expr :=
  conditions.foldr Expr.and (.lit (.bool true))

def permit (id : String) (action : EntityUID) (conditions : List Expr) : Policy :=
  { id, effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := all conditions }] }

def trainingPermit : Policy := permit "model-training" train [
  eq (attr .principal "kind") (string "trainer"),
  eq (attr .resource "kind") (string "run"),
  eq (attr .context "purpose") (string "research"),
  attr .context "approvalValid",
  attr .context "deidentificationAttested"]

def publicationPermit : Policy := permit "model-publication" publish [
  eq (attr .principal "kind") (string "publisher"),
  eq (attr .resource "kind") (string "model"),
  eq (attr .context "purpose") (string "publication"),
  attr .context "approvalValid",
  attr .context "modelReviewed",
  attr .context "sinkBound"]

def inferencePermit : Policy := permit "clinical-inference" infer [
  eq (attr .principal "kind") (string "clinician"),
  eq (attr .resource "kind") (string "endpoint"),
  eq (attr .context "purpose") (string "treatment"),
  attr .context "patientBound",
  attr .context "clinicalValidationCurrent",
  attr .context "auditReady"]

def lineageControl : LineageUse :=
  { policyId := "model-lineage-current",
    actionScope := .actionInAny [train, publish, infer] }

def incidentControl : Veto :=
  { policyId := "model-release-incident",
    actionScope := .actionInAny [publish, infer],
    denyWhen := .lit (.bool true) }

def integratedResult : Except LeanPoo.Object.CombineError Model := do
  let training ← (Model.define "Training" [.extend trainingPermit]).mapError .c4
  let publication ← (Model.define "Publication" [.extend publicationPermit]).mapError .c4
  let clinical ← (Model.define "Clinical" [.extend inferencePermit]).mapError .c4
  let lineage ← (Model.define "Lineage" [lineageControl.edit .introduce]).mapError .c4
  training.combine "Training"
    [(publication, "Publication"), (clinical, "Clinical"), (lineage, "Lineage")]
    "MedicalModel"

def modelResult : Except LeanPoo.Object.CombineError Model := do
  let integrated ← integratedResult
  let incident ← (integrated.extend "ModelIncident" "MedicalModel"
    [incidentControl.edit .introduce]).mapError .c4
  (incident.extend "Recovered" "ModelIncident"
    [incidentControl.edit .withdraw]).mapError .c4

def model : Model := modelResult.toOption.get (by native_decide)

/-- Compile-stage capability for this schema-free semantic fixture. -/
protected def program : CedarPooSpec.Functional.Compilation model :=
  CedarPooSpec.Functional.compilation model

/-- The grant source, target, action, purpose, and governance revision must
    all match. The Host supplies authenticated grant and clock values. -/
def trainingGrant : ScopedApproval :=
  { id := "study-approval-42", approver := studyReviewer, actor := trainer,
    operation := train, purpose := "research", source := jointDataset,
    target := jointRun, revision := 1, expiresAt := 100 }

def publicationGrant : ScopedApproval :=
  { id := "model-release-42", approver := releaseReviewer, actor := publisher,
    operation := publish, purpose := "publication", source := jointModel,
    target := jointEndpoint, revision := 1, expiresAt := 100 }

structure Facts where
  artifact : String
  lineageRevision : String
  lineageAvailable : Bool
  purpose : String
  approvalValid : Bool := false
  deidentificationAttested : Bool := false
  modelReviewed : Bool := false
  sinkBound : Bool := false
  patientBound : Bool := false
  clinicalValidationCurrent : Bool := false
  auditReady : Bool := false

def request (actor action resource : EntityUID) (facts : Facts) : Request :=
  ⟨actor, action, resource, Map.make [
    ("targetArtifact", .prim (.string facts.artifact)),
    ("lineageRevision", .prim (.string facts.lineageRevision)),
    ("lineageAvailable", .prim (.bool facts.lineageAvailable)),
    ("purpose", .prim (.string facts.purpose)),
    ("approvalValid", .prim (.bool facts.approvalValid)),
    ("deidentificationAttested", .prim (.bool facts.deidentificationAttested)),
    ("modelReviewed", .prim (.bool facts.modelReviewed)),
    ("sinkBound", .prim (.bool facts.sinkBound)),
    ("patientBound", .prim (.bool facts.patientBound)),
    ("clinicalValidationCurrent", .prim (.bool facts.clinicalValidationCurrent)),
    ("auditReady", .prim (.bool facts.auditReady))]⟩

end CedarPooSpec.ModelStewardshipExample
