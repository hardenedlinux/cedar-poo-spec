import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Revision
import CedarPooSpec.PolicyJson
import CedarPooSpec.Authorization.Compound
import Cedar.Validation.RequestEntityValidator

/-!
CHAI (Burbano et al., 2026) changed a driving LVLM's high-level crosswalk
decision from braking to acceleration using attacker-controlled visual text.
This example models a proposed authorization boundary for such commands. It
does not run a VLA, detect the visual attack, verify sensors, or control a car.
-/

namespace CedarPooSpec.VlaCommandBoundaryExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Soundness CedarPooSpec.PolicyValidation LeanPoo.Proof

def plannerType : EntityType := ⟨"DrivingPlanner", []⟩
def segmentType : EntityType := ⟨"RoadSegment", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def planner : EntityUID := ⟨plannerType, "vla-adapter"⟩
def crosswalk : EntityUID := ⟨segmentType, "occupied-crosswalk"⟩
def affectedClear : EntityUID := ⟨segmentType, "clear-affected-cohort"⟩
def unaffectedClear : EntityUID := ⟨segmentType, "clear-other-cohort"⟩
def accelerate : EntityUID := ⟨actionType, "accelerate"⟩
def brake : EntityUID := ⟨actionType, "brake"⟩
def report : EntityUID := ⟨actionType, "report-hazard"⟩

def emptyEntry : EntitySchemaEntry := .standard ⟨Set.empty, Map.empty, none⟩
def segmentEntry : EntitySchemaEntry := .standard ⟨Set.empty, Map.make [
  ("pedestriansPresent", .required (.bool .anyBool)),
  ("affectedCohort", .required (.bool .anyBool))], none⟩
def contextType : RecordType := Map.make [
  ("routeApproved", .required (.bool .anyBool)),
  ("sceneTextPromoted", .required (.bool .anyBool)),
  ("modelAffected", .required (.bool .anyBool))]
def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [plannerType], Set.make [segmentType], Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [(plannerType, emptyEntry), (segmentType, segmentEntry)],
    Map.make [(accelerate, actionEntry), (brake, actionEntry),
      (report, actionEntry)]⟩

def emptyData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }
def segmentData (pedestrians affected : Bool) : EntityData :=
  { attrs := Map.make [
      ("pedestriansPresent", .prim (.bool pedestrians)),
      ("affectedCohort", .prim (.bool affected))],
    ancestors := Set.empty, tags := Map.empty }
def entities : Entities := Map.make [
  (planner, emptyData),
  (crosswalk, segmentData true true),
  (affectedClear, segmentData false true),
  (unaffectedClear, segmentData false false),
  (accelerate, actionSchemaEntryToEntityData actionEntry),
  (brake, actionSchemaEntryToEntityData actionEntry),
  (report, actionSchemaEntryToEntityData actionEntry)]

def ctx (name : String) : Expr := .getAttr (.var .context) name
def segmentFact (name : String) : Expr := .getAttr (.var .resource) name
def policy (id : String) (effect : Effect) (action : EntityUID)
    (body : Expr) : Policy :=
  { id, effect,
    principalScope := .principalScope (.eq planner),
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body }] }

def accelerationBase : Policy :=
  policy "planner-acceleration" .permit accelerate (ctx "routeApproved")
def braking : Policy :=
  policy "safe-braking" .permit brake (.lit (.bool true))
def hazardReport : Policy :=
  policy "hazard-report" .permit report (.lit (.bool true))
def accelerationWithIndependentSafety : Policy :=
  { accelerationBase with condition := [
      { kind := .when,
        body := .and (ctx "routeApproved")
          (.unaryApp .not (segmentFact "pedestriansPresent")) }] }
def untrustedSceneText : Policy :=
  policy "scene-text-instruction-veto" .forbid accelerate
    (ctx "sceneTextPromoted")
def affectedModelQuarantine : Policy :=
  policy "affected-vla-quarantine" .forbid accelerate
    (.and (ctx "modelAffected") (segmentFact "affectedCohort"))

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [
        .extend accelerationBase, .extend braking, .extend hazardReport] }] }
  let safety ← base.extend "Safety" "Base" [.overlay accelerationWithIndependentSafety]
  let provenance ← safety.extend "Provenance" "Base" [.extend untrustedSceneText]
  let integrated ← provenance.mix "Integrated" ["Safety", "Provenance"]
  let incident ← integrated.extend "Incident" "Integrated"
    [.extend affectedModelQuarantine]
  incident.extend "Recovered" "Incident" [.remove affectedModelQuarantine.id]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)


structure Facts where
  routeApproved : Bool := true
  sceneTextPromoted : Bool := false
  modelAffected : Bool := false

def context (facts : Facts) : Map String Value := Map.make [
  ("routeApproved", .prim (.bool facts.routeApproved)),
  ("sceneTextPromoted", .prim (.bool facts.sceneTextPromoted)),
  ("modelAffected", .prim (.bool facts.modelAffected))]
def request (action segment : EntityUID) (facts : Facts) : Request :=
  ⟨planner, action, segment, context facts⟩
def authorized
     (root : String) (action segment : EntityUID) (facts : Facts)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.VlaCommandBoundaryExample.model CedarPooSpec.VlaCommandBoundaryExample.schema :=
      CedarPooSpec.VlaCommandBoundaryExample.program) : Bool :=
  match programContext.authorizeLayers [(root, request action segment facts)] entities with
  | .error _ => false
  | .ok receipts => CedarPooSpec.Authorization.Compound.layersAllowed receipts

def cases : List (String × String × EntityUID × EntityUID × Facts × Bool) := [
  ("base-accelerates-at-occupied-crosswalk", "Base", accelerate, crosswalk, {}, true),
  ("safety-blocks-occupied-crosswalk", "Safety", accelerate, crosswalk, {}, false),
  ("provenance-blocks-promoted-scene-text", "Provenance", accelerate,
    affectedClear, { sceneTextPromoted := true }, false),
  ("provenance-alone-misses-pedestrians", "Provenance", accelerate,
    crosswalk, {}, true),
  ("integrated-blocks-pedestrians", "Integrated", accelerate, crosswalk, {}, false),
  ("integrated-blocks-scene-text", "Integrated", accelerate,
    affectedClear, { sceneTextPromoted := true }, false),
  ("integrated-allows-clear-authorized-route", "Integrated", accelerate,
    affectedClear, {}, true),
  ("integrated-rejects-unapproved-route", "Integrated", accelerate,
    affectedClear, { routeApproved := false }, false),
  ("braking-survives-prompt-injection", "Integrated", brake, crosswalk,
    { sceneTextPromoted := true }, true),
  ("affected-cohort-quarantined", "Incident", accelerate, affectedClear,
    { modelAffected := true }, false),
  ("other-cohort-keeps-clear-route", "Incident", accelerate, unaffectedClear,
    { modelAffected := true }, true),
  ("quarantine-retains-braking", "Incident", brake, crosswalk,
    { modelAffected := true }, true),
  ("quarantine-retains-hazard-report", "Incident", report, crosswalk,
    { modelAffected := true }, true),
  ("recovered-cohort-can-accelerate", "Recovered", accelerate, affectedClear,
    { modelAffected := true }, true),
  ("recovery-keeps-pedestrian-veto", "Recovered", accelerate, crosswalk,
    { modelAffected := true }, false)]

def casesExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.VlaCommandBoundaryExample.model CedarPooSpec.VlaCommandBoundaryExample.schema :=
      CedarPooSpec.VlaCommandBoundaryExample.program) : Bool :=
  cases.all (fun (_, root, action, segment, facts, expected) =>
    (authorized (programContext := programContext)) root action segment facts == expected)
theorem casesExactFully : casesExact = true := by native_decide

def rootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.VlaCommandBoundaryExample.model CedarPooSpec.VlaCommandBoundaryExample.schema :=
      CedarPooSpec.VlaCommandBoundaryExample.program) : Bool :=
  ["Base", "Safety", "Provenance", "Integrated", "Incident", "Recovered"].all fun root =>
    (programContext.publish root).isOk
theorem rootsValidatedFully : rootsValidated = true := by native_decide

def incidentRevision : Revision :=
  (model.compileRevision "Integrated" "Incident").toOption.get (by native_decide)
theorem incidentDelta :
    incidentRevision.changedPolicyIds = [affectedModelQuarantine.id] ∧
    incidentRevision.freshPolicies = [affectedModelQuarantine] := by native_decide
def recoveryRevision : Revision :=
  (model.compileRevision "Incident" "Recovered").toOption.get (by native_decide)
theorem recoveryDelta :
    recoveryRevision.changedPolicyIds = [affectedModelQuarantine.id] ∧
    recoveryRevision.freshPolicies = [] := by native_decide

def witness : Request := request accelerate affectedClear { modelAffected := true }
def incidentBefore : AuthorizationSnapshot :=
  incidentRevision.beforeSnapshot schema witness entities
theorem incidentBaseline : Certificate incidentBefore.proofObject :=
  incidentBefore.certificateOfChecks (by native_decide)
private theorem okOfIsOk {ε : Type} (result : Except ε Unit)
    (accepted : result.isOk = true) : result = .ok () := by
  cases result with
  | ok value => cases value; rfl
  | error _ => cases accepted
theorem incidentFreshCertificates :
    ∀ policy ∈ incidentRevision.freshPolicies,
      Certificate (Snapshot.mk policy schema).proofObject := by
  intro policy member
  rw [incidentDelta.2] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst policy
  exact (Snapshot.mk affectedModelQuarantine schema).certificate
    (okOfIsOk _ (by native_decide))
theorem incidentCertificate :
    Certificate (incidentRevision.afterSnapshot schema witness entities).proofObject :=
  incidentRevision.authorizationCertificate schema witness entities
    (by simpa [incidentBefore] using incidentBaseline) incidentFreshCertificates
example : Cedar.Thm.AllEvaluateToBool incidentRevision.afterPolicies witness entities :=
  certifiedAuthorizationSound
    (incidentRevision.afterSnapshot schema witness entities) incidentCertificate

def recoveryBefore : AuthorizationSnapshot :=
  recoveryRevision.beforeSnapshot schema witness entities
theorem recoveryBaseline : Certificate recoveryBefore.proofObject :=
  recoveryBefore.certificateOfChecks (by native_decide)
theorem recoveryCertificate :
    Certificate (recoveryRevision.afterSnapshot schema witness entities).proofObject :=
  recoveryRevision.authorizationCertificate schema witness entities
    (by simpa [recoveryBefore] using recoveryBaseline)
    (by intro policy member; simp [recoveryDelta.2] at member)
example : Cedar.Thm.AllEvaluateToBool recoveryRevision.afterPolicies witness entities :=
  certifiedAuthorizationSound
    (recoveryRevision.afterSnapshot schema witness entities) recoveryCertificate

end CedarPooSpec.VlaCommandBoundaryExample
