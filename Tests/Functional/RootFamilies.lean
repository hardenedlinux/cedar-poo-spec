import Tests.Functional.Capabilities
import Examples.Governance.AttestedDataAccessExport
import Examples.Cloud.Pipeline.ReplayExport
import Examples.Enterprise.Agent.DataFlow.ValidatedExport

/-! Independent pre-C1 export algorithms and multi-root admission controls. -/


/-! Export attested-data POO revisions and Lean-computed authorization receipts. -/

namespace CedarPooSpec.RootFamiliesTest.Reference.Attested

open CedarPooSpec.AttestedDataAccessExample
open CedarPooSpec.AttestedManifest

private def case (name : String) (root : Root) (req : Cedar.Spec.Request) :
    Except String Lean.Json :=
  PolicyJson.authorizationCase name root.artifactRevision model root.name req entities

def rows : Except String (List Lean.Json) := do
  let stable ← unchangedCases.mapM fun (name, req, _) => do
    let before ← case s!"{name}-baseline" .baseline req
    let after ← case s!"{name}-updated" .strengthened req
    return [before, after]
  let staleBefore ← case "stale-attestation-baseline" .baseline
    (request customerDataset { attestationFresh := false })
  let staleAfter ← case "stale-attestation-updated" .strengthened
    (request customerDataset { attestationFresh := false })
  let inherited ← case "pre-integration-broad-permit" .ownerOnly
    (request financeDataset {})
  return stable.flatten ++ [staleBefore, staleAfter, inherited]

def manifest : Except String Lean.Json := do
  return Lean.Json.mkObj [("cases", Lean.toJson (← rows))]

end CedarPooSpec.RootFamiliesTest.Reference.Attested

/-! Export the same stage decisions checked in Lean for Cedar Rust replay. -/

namespace CedarPooSpec.RootFamiliesTest.Reference.Threat

open CedarPooSpec.Cloud.Pipeline.GoogleThreatCase

def manifest : Except String Lean.Json := do
  let rows ← cases.mapM fun (name, root, resource, facts, _) =>
    CedarPooSpec.PolicyJson.authorizationCase name root model root
      (request resource facts) entities
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.RootFamiliesTest.Reference.Threat

namespace CedarPooSpec.RootFamiliesTest.Reference.Flow

open CedarPooSpec.AgentDataFlowExample

def wellFormedRows : Except String (List Lean.Json) := do
  let mut rows : List Lean.Json := []
  for (name, readRoot, publishRoot, source, repo, origin, approver, approved, _) in cases do
    for ((root, req), index) in
        (checks readRoot publishRoot source repo origin approver approved).zipIdx do
      let receipt ← CedarPooSpec.PolicyJson.authorizationCase
        s!"{name}-layer-{index}" root.toLower dataModel root req dataEntities
      rows := rows ++ [receipt]
  return rows

def manifest : Except String Lean.Json := do
  let mut rows ← wellFormedRows
  for ((root, req), index) in malformedChecks.zipIdx do
    let receipt ← CedarPooSpec.PolicyJson.authorizationCase
      s!"malformed-review-layer-{index}" root.toLower dataModel root req dataEntities
    rows := rows ++ [receipt]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.RootFamiliesTest.Reference.Flow

namespace CedarPooSpec.RootFamiliesTest.Reference.ValidatedFlow

open CedarPooSpec.AgentDataFlowExample
open CedarPooSpec.AgentDelegationExample

/-- Replay identical allow and deny requests through both construction roots. -/
def dispatchComparisonRows : Except String (List Lean.Json) := do
  let requests := [
    ("allow", publishRequest publicDoc publicRepo admin reviewer true),
    ("deny", publishRequest internalDoc publicRepo admin reviewer true)]
  let mut rows : List Lean.Json := []
  for (label, req) in requests do
    for root in ["PublishGoverned", "PublishDispatched"] do
      let receipt ← CedarPooSpec.PolicyJson.authorizationCase
        s!"dispatch-{label}-{root.toLower}" root.toLower dataModel root req dataEntities
      rows := rows ++ [receipt]
  return rows

def manifest : Except String Lean.Json := do
  let rows ← CedarPooSpec.RootFamiliesTest.Reference.Flow.wellFormedRows
  let comparisons ← dispatchComparisonRows
  CedarPooSpec.SchemaJson.validatedManifest
    dataSchema (rows ++ comparisons)

end CedarPooSpec.RootFamiliesTest.Reference.ValidatedFlow
namespace CedarPooSpec.RootFamiliesTest

open Cedar.Spec Cedar.Validation CedarPooSpec.Functional

private def wire (result : Except String Lean.Json) : Except String String :=
  result.map Lean.Json.compress

example : wire AttestedDataAccessExport.manifest = wire Reference.Attested.manifest := by
  native_decide
example : wire Cloud.Pipeline.GoogleThreatCase.manifest = wire Reference.Threat.manifest := by
  native_decide
example : wire AgentDataFlowExport.manifest = wire Reference.Flow.manifest := by
  native_decide
example : wire AgentDataFlowValidatedExport.manifest = wire Reference.ValidatedFlow.manifest := by
  native_decide

private def project {model : PolicyModules.Model} {entities : Entities}
    (layers : List (Authorization.Compound.LayerReceipt model entities)) :=
  layers.map fun layer => (layer.root, layer.request, layer.policies, layer.response)

namespace Flow
open AgentDataFlowExample AgentDelegationExample

def parity (inputs : List (String × Request)) : Bool := decide (
    (program.authorizeLayers inputs dataEntities).toOption.map project =
    (Authorization.Compound.authorizeLayers dataModel inputs dataEntities).toOption.map project)

example : cases.all (fun (_, readRoot, publishRoot, source, repo, origin, approver, approved, _) =>
    parity (checks readRoot publishRoot source repo origin approver approved)) = true := by
  native_decide
example : parity AgentDataFlowExample.malformedChecks = true := by native_decide
-- Repetition, reordering and empty input retain the legacy observable behavior.
example : parity (AgentDataFlowExample.malformedChecks.reverse ++ AgentDataFlowExample.malformedChecks ++ AgentDataFlowExample.malformedChecks) = true := by
  native_decide
example : parity [] = true ∧
    (program.authorizeLayers [] dataEntities).toOption.map Authorization.Compound.layersAllowed =
      some false := by native_decide

example : (match program.authorizeLayers
    [("ReadTenant", readRequest publicDoc admin), ("missing-first", malformedReviewRequest),
      ("missing-second", malformedReviewRequest)] dataEntities with
  | .error (.context root (.composition _)) => root == "missing-first"
  | _ => false) = true := by native_decide

example : dataModel.modules.all (fun item => decide (
    (program.publish item.name).toOption.map (fun publication => publication.json.compress) =
    (PolicyJson.publish dataModel item.name dataSchema).toOption.map (fun publication => publication.json.compress))) = true := by
  native_decide

-- Removing all entities must not retain a decision from the earlier snapshot.
example : (program.authorizeLayers
    (checks "ReadTenant" "PublishGoverned" publicDoc publicRepo admin reviewer true)
    Cedar.Data.Map.empty).toOption.map Authorization.Compound.layersAllowed = some false := by
  native_decide
end Flow

namespace Threat
open Cloud.Pipeline.GoogleThreatCase
example : cases.all (fun (_, root, resource, facts, _) =>
    allowed root resource facts == (match model.compile root with
    | .error _ => false
    | .ok policies =>
      let response := isAuthorized (request resource facts) entities policies
      response.decision == .allow && response.erroringPolicies.isEmpty)) = true := by
  native_decide
example : model.modules.all (fun item => decide (
    (program.publish item.name).toOption.map (fun publication => publication.json.compress) =
    (PolicyJson.publish model item.name schema).toOption.map (fun publication => publication.json.compress))) = true := by
  native_decide
end Threat

namespace Attested
open AttestedDataAccessExample AttestedManifest

def classifiedProgram : Program model schemaWithClassification :=
  (prepareProgram standard model schemaWithClassification (model.modules.map (·.name))).toOption.get
    (by native_decide)

-- Schema evidence cannot be reused as a new schema's Program.
example : Program model schemaWithClassification := by
  fail_if_success exact program
  exact classifiedProgram

def withoutAudit : PolicyModules.Model :=
  { model with modules := model.modules.filter (fun item => item.name != Root.audit.name) }
def withoutAuditProgram : Program withoutAudit schema :=
  (prepareProgram standard withoutAudit schema [Root.baseline.name]).toOption.get (by native_decide)

example : Program withoutAudit schema := by
  fail_if_success exact program
  exact withoutAuditProgram

example : (program.publish Root.audit.name).isOk = true ∧
    (withoutAuditProgram.publish Root.audit.name).isOk = false := by native_decide

example : model.modules.all (fun item => decide (
    (program.publish item.name).toOption.map (fun publication => publication.json.compress) =
    (PolicyJson.publish model item.name schema).toOption.map (fun publication => publication.json.compress))) = true := by
  native_decide
example : (prepareProgram standard model SchemaProjectionTest.danglingAncestorSchema
    [Root.baseline.name]).isOk = false := by native_decide

example : unchangedCases.all (fun (_, req, _) =>
    [Root.baseline, Root.strengthened, Root.audit, Root.reordered, Root.ownerOnly].all fun root =>
      (program.authorize root.name [req] entities).toOption.map (·.responses) ==
        (classifiedProgram.authorize root.name [req] entities).toOption.map (·.responses)) = true := by
  native_decide

example : (program.authorize Root.baseline.name
      [request customerDataset { attestationFresh := false }] entities).toOption.map (·.allowed) = some true ∧
    (program.authorize Root.strengthened.name
      [request customerDataset { attestationFresh := false }] entities).toOption.map (·.allowed) = some false := by
  native_decide
end Attested

open Lean in
run_cmd do
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  for declaration in [``CedarPooSpec.Functional.Ready.authorizeLayer_response,
      ``CedarPooSpec.Functional.Program.authorizeLayers_append] do
    let dependencies ← collectAxioms declaration
    for dependency in dependencies do
      unless allowed.contains dependency.toString do
        throwError "Functional multi-root axiom boundary changed: {declaration}: {dependency}"
  logInfo "FUNCTIONAL-CEDAR-ROOTS-AXIOMS-OK two universal layer proofs"

end CedarPooSpec.RootFamiliesTest
