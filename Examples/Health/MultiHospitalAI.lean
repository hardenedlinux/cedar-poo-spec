import CedarPooSpec.Functional.Compilation
import CedarPooSpec.Data.Lineage
import CedarPooSpec.Data.LineageUse
import CedarPooSpec.Pseudonymization.TokenCatalog
import CedarPooSpec.PolicyJson
import CedarPooSpec.SchemaJson

/-!
Synthetic longitudinal study across two hospitals. A research consent change
withdraws one source from this study, invalidating only its descendants.
Clinical emergency access is an independent treatment owner. The example
models decisions; hospitals and a Host own real records, consent, and effects.
-/

namespace CedarPooSpec.MultiHospitalAIExample

open Cedar.Spec Cedar.Data CedarPooSpec.PolicyModules
open CedarPooSpec.Data CedarPooSpec.Data.Lineage
open CedarPooSpec.Pseudonymization

def actorType : EntityType := ⟨"Actor", []⟩
def artifactType : EntityType := ⟨"Artifact", []⟩
def actionType : EntityType := ⟨"Action", []⟩

def researcher : EntityUID := ⟨actorType, "study-researcher"⟩
def clinician : EntityUID := ⟨actorType, "on-call-clinician"⟩
def jointIndex : EntityUID := ⟨artifactType, "joint-index"⟩
def studyResult : EntityUID := ⟨artifactType, "study-result"⟩
def hospitalB : EntityUID := ⟨artifactType, "hospital-b-record"⟩
def derive : EntityUID := ⟨actionType, "derive-ai-context"⟩
def release : EntityUID := ⟨actionType, "release-study-result"⟩
def emergencyRead : EntityUID := ⟨actionType, "emergency-read"⟩

def catalog : Catalog := ⟨[
  ⟨"hospital-a-record", .source, []⟩,
  ⟨"hospital-b-record", .source, []⟩,
  ⟨"hospital-a-fragment", .fragment, ["hospital-a-record"]⟩,
  ⟨"hospital-b-fragment", .fragment, ["hospital-b-record"]⟩,
  ⟨"joint-index", .index, ["hospital-a-fragment", "hospital-b-fragment"]⟩,
  ⟨"agent-prompt", .prompt, ["joint-index"]⟩,
  ⟨"study-result", .result, ["agent-prompt"]⟩]⟩

/-- Both hospitals join only inside this study's declared key domain. A
    provider receipt must still bind the actual key and context tweak. -/
def hospitalAProfile : TokenProfile :=
  { mode := .aesSiv, scope := "study-42", lineage :=
    { tenant := "research-network", keyDomain := "study-42", tokenKeyVersion := "dek-1", transformVersion := "normalize-1", wrappingVersion := "kek-1" } }

def hospitalBProfile : TokenProfile :=
  { hospitalAProfile with lineage :=
    { hospitalAProfile.lineage with wrappingVersion := "kek-2" } }

def entity (attrs : List (String × Value)) : EntityData :=
  { attrs := Map.make attrs, ancestors := Set.empty, tags := Map.empty }

def actorData (kind : String) : EntityData :=
  entity [("kind", .prim (.string kind))]

def artifactData (id revision : String) : EntityData :=
  let kind := if id == "joint-index" then "index"
    else if id == "study-result" then "result" else "clinical-source"
  entity [("artifactId", .prim (.string id)), ("kind", .prim (.string kind)),
    ("lineageRevision", .prim (.string revision))]

def entities (revision : String) : Entities := Map.make [
  (researcher, actorData "researcher"),
  (clinician, actorData "clinician"),
  (jointIndex, artifactData "joint-index" revision),
  (studyResult, artifactData "study-result" revision),
  (hospitalB, artifactData "hospital-b-record" revision)]

def attr (source : Var) (name : String) : Expr :=
  .getAttr (.var source) name
def fact (name : String) : Expr := attr .context name
def eq (left right : Expr) : Expr := .binaryApp .eq left right
def string (value : String) : Expr := .lit (.string value)

def permit (id : String) (action : EntityUID) (body : Expr) : Policy :=
  { id, effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body }] }

def researchBody : Expr :=
  .and (eq (attr .principal "kind") (string "researcher"))
    (.and (eq (fact "purpose") (string "research"))
      (.and (fact "studyApprovalActive")
        (.and (fact "modelApproved") (fact "tokenCompatible"))))

def derivePermit : Policy := permit "research-derive" derive
  (.and researchBody (eq (attr .resource "kind") (string "index")))
def releasePermit : Policy := permit "research-release" release
  (.and researchBody
    (.and (eq (attr .resource "kind") (string "result"))
      (.and (fact "resultReviewed") (fact "auditReady"))))
def emergencyPermit : Policy := permit "clinical-emergency" emergencyRead
  (.and (eq (attr .principal "kind") (string "clinician"))
    (.and (eq (fact "purpose") (string "treatment"))
      (.and (eq (attr .resource "kind") (string "clinical-source"))
        (.and (fact "patientBound")
          (.and (fact "emergencyActive") (fact "auditReady"))))))

def lineageControl : LineageUse :=
  { policyId := "research-lineage-current",
    actionScope := .actionInAny [derive, release] }

def incidentControl : CedarPooSpec.Governance.Veto :=
  { policyId := "research-output-incident",
    actionScope := .actionScope (.eq release),
    denyWhen := .lit (.bool true) }

/-- Research, lineage, and treatment are independent POO owners. -/
def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [{ name := "Base" }] }
  let research ← base.extend "Research" "Base"
    [.extend derivePermit, .extend releasePermit]
  let lineage ← research.extend "Lineage" "Base"
    [lineageControl.edit .introduce]
  let clinical ← lineage.extend "Clinical" "Base"
    [.extend emergencyPermit]
  let integrated ← clinical.mix "HospitalStudy"
    ["Research", "Lineage", "Clinical"]
  let incident ← integrated.extend "OutputIncident" "HospitalStudy"
    [incidentControl.edit .introduce]
  incident.extend "Recovered" "OutputIncident"
    [incidentControl.edit .withdraw]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Compile-stage capability for this schema-free semantic fixture. -/
protected def program : CedarPooSpec.Functional.Compilation model :=
  CedarPooSpec.Functional.compilation model


structure Facts where
  targetArtifact : String
  lineageRevision : String := "r1"
  lineageAvailable : Bool
  purpose : String := "research"
  studyApprovalActive : Bool := true
  modelApproved : Bool := true
  tokenCompatible : Bool := true
  resultReviewed : Bool := true
  auditReady : Bool := true
  emergencyActive : Bool := false
  patientBound : Bool := false

def factsFor (target : String) (withdrawn : List String)
    (revision : String := "r1")
    (bProfile : TokenProfile := hospitalBProfile) : Except Lineage.Error Facts := do
  let available ← catalog.available withdrawn target
  let facts : Facts := { targetArtifact := target, lineageRevision := revision, lineageAvailable := available, tokenCompatible := hospitalAProfile.sameRecipe bProfile }
  return facts

def request (actor action resource : EntityUID) (facts : Facts) : Request :=
  ⟨actor, action, resource, Map.make [
    ("targetArtifact", .prim (.string facts.targetArtifact)),
    ("lineageRevision", .prim (.string facts.lineageRevision)),
    ("lineageAvailable", .prim (.bool facts.lineageAvailable)),
    ("purpose", .prim (.string facts.purpose)),
    ("studyApprovalActive", .prim (.bool facts.studyApprovalActive)),
    ("modelApproved", .prim (.bool facts.modelApproved)),
    ("tokenCompatible", .prim (.bool facts.tokenCompatible)),
    ("resultReviewed", .prim (.bool facts.resultReviewed)),
    ("auditReady", .prim (.bool facts.auditReady)),
    ("emergencyActive", .prim (.bool facts.emergencyActive)),
    ("patientBound", .prim (.bool facts.patientBound))]⟩

def decision
     (root revision : String) (req : Request)
    (programContext : CedarPooSpec.Functional.Compilation CedarPooSpec.MultiHospitalAIExample.model :=
      CedarPooSpec.MultiHospitalAIExample.program) : Option Decision := do
  let response ← (programContext.response root req (entities revision)).toOption
  if response.erroringPolicies.isEmpty then some response.decision else none

def researchDecision
     (root revision : String) (action resource : EntityUID)
    (target : String) (withdrawn : List String)
    (bProfile : TokenProfile := hospitalBProfile)
    (programContext : CedarPooSpec.Functional.Compilation CedarPooSpec.MultiHospitalAIExample.model :=
      CedarPooSpec.MultiHospitalAIExample.program) :
    Except Lineage.Error (Option Decision) := do
  let facts ← factsFor target withdrawn revision bProfile
  return (decision (programContext := programContext)) root revision (request researcher action resource facts)

def clinicalDecision
     (revision : String)
    (programContext : CedarPooSpec.Functional.Compilation CedarPooSpec.MultiHospitalAIExample.model :=
      CedarPooSpec.MultiHospitalAIExample.program) : Option Decision :=
  (decision (programContext := programContext)) "HospitalStudy" revision <|
    request clinician emergencyRead hospitalB
      { targetArtifact := "hospital-b-record", lineageRevision := revision,
        lineageAvailable := false, purpose := "treatment",
        emergencyActive := true, patientBound := true }

end CedarPooSpec.MultiHospitalAIExample
