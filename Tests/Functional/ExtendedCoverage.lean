import Examples.Cloud.Pipeline.DeploymentReplayExport
import Examples.Cloud.DataProtection.ReplayExport
import Examples.Health.PseudonymizationExport

/-! Independent pre-extension algorithms; current fixtures retain their own
production-boundary checks and use the selected checked Cedar authorizer. -/


namespace CedarPooSpec.ExtendedCoverageTest.Reference.Deployment
open CedarPooSpec.Cloud.Pipeline.DeploymentCase CedarPooSpec.Cloud.Pipeline

def manifest : Except String Lean.Json := do
  let rows ← (choices.flatMap fun choice =>
    [(s!"{choice.name}-promotion", choice.root,
        GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline),
      (s!"{choice.name}-deployment", choice.root, deployRequest choice)]).mapM
      fun (name, root, request) =>
        CedarPooSpec.PolicyJson.authorizationCase name root model root
          request entities
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.ExtendedCoverageTest.Reference.Deployment

namespace CedarPooSpec.ExtendedCoverageTest.Reference.Sdp
open CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease

open CedarPooSpec.Cloud.Pipeline

def manifest : Except String Lean.Json := do
  let rows ← (choices.flatMap fun choice =>
    [(s!"{choice.name}-pipeline", choice.root,
        GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline),
      (s!"{choice.name}-transform", choice.root, transformRequest choice)]).mapM
      fun (name, root, request) =>
        CedarPooSpec.PolicyJson.authorizationCase name root model root
          request entities
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.ExtendedCoverageTest.Reference.Sdp

/-! Export each composed root with the same source and target entities used by
the Lean decision proof. Rust Cedar validates the schema and replays the cases. -/

namespace CedarPooSpec.ExtendedCoverageTest.Reference.Pseudonymization

open CedarPooSpec.PseudonymizationExample

def manifest : Except String Lean.Json := do
  unless hmacCatalogSeparated datasets do
    throw "cross-scope HMAC key reuse in published dataset catalog"
  let rows ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.PolicyJson.authorizationCase name root model root req entities
  CedarPooSpec.SchemaJson.validatedManifest schema rows

def deployableRoots : List PseudonymizationExample.Deployment.Root :=
  [.hospitalSiv, .randomizedGcm, .oneWayHmac,
   .resultRelease, .agentIncident, .recovered]

/-- Deployment artifacts have a typed allowlist; the migration ancestor is
    available only to the authorization regression manifest above. -/
def deploymentManifest : Except String Lean.Json := do
  unless hmacCatalogSeparated datasets do
    throw "cross-scope HMAC key reuse in published dataset catalog"
  let roots ← deployableRoots.mapM fun root => do
    let publication ← (CedarPooSpec.PolicyJson.publish model root.name schema).mapError
      (fun _ => "deployable root failed Cedar publication")
    return Lean.Json.mkObj [
      ("root", Lean.toJson root.name), ("policies", publication.json)]
  return Lean.toJson roots

end CedarPooSpec.ExtendedCoverageTest.Reference.Pseudonymization
namespace CedarPooSpec.ExtendedCoverageTest.Reference.Lifecycle
open CedarPooSpec.PseudonymizationExample.Lifecycle CedarPooSpec.PseudonymizationExample
open Cedar.Spec (Request isAuthorized)

def allowed (state : State) (effect : Effect) : Bool :=
  let req := request effect.actor effect.step.action effect.source (facts state effect)
  match model.compile effect.root.name with
  | .error _ => false
  | .ok policies =>
    let response := isAuthorized req entities policies
    response.decision == .allow && response.erroringPolicies.isEmpty

def prepare (state : State) (effect : Effect) : Option Ticket :=
  if effect.payloadDigest.isEmpty ||
      (effect.root == .randomizedGcm && effect.iv.isEmpty) ||
      !allowed state effect then none
  else some ⟨effect.root, state.policyRevision,
    state.approvalRevision, state.epoch, effect⟩

/-- The return value is a modeled state transition, not a record that an
    external encryption, query, or plaintext release actually took place. -/
def redeem (state : State) (ticket : Ticket) (effect : Effect) : Option State :=
  if ticket.root != effect.root ||
      ticket.policyRevision != state.policyRevision ||
      ticket.approvalRevision != state.approvalRevision ||
      ticket.epoch != state.epoch || ticket.effect != effect ||
      !allowed state effect then none
  else
    let next := { state with epoch := state.epoch + 1, auditLog := state.auditLog ++ [effect.payloadDigest] }
    let next := if effect.step == .release then
      { next with releaseBudget := state.releaseBudget - 1 }
      else next
    let next := if effect.step == .ingest && effect.iv != "" then
      { next with usedIvs := effect.iv :: state.usedIvs }
      else next
    some next

end CedarPooSpec.ExtendedCoverageTest.Reference.Lifecycle
namespace CedarPooSpec.ExtendedCoverageTest
open Cedar.Spec CedarPooSpec.Functional

private def wire (result : Except String Lean.Json) := result.map Lean.Json.compress

example : wire Cloud.Pipeline.DeploymentCase.manifest = wire Reference.Deployment.manifest := by
  native_decide
example : wire Cloud.DataProtection.GoogleSdpRelease.manifest = wire Reference.Sdp.manifest := by
  native_decide
example : wire PseudonymizationExport.manifest = wire Reference.Pseudonymization.manifest := by native_decide
example : wire PseudonymizationExport.deploymentManifest =
    wire Reference.Pseudonymization.deploymentManifest := by native_decide

namespace Deployment
open CedarPooSpec.Cloud.Pipeline.DeploymentCase CedarPooSpec.Cloud.Pipeline

example : choices.all (fun choice =>
    admitted choice == (promotionAllowed choice && deploymentAllowed choice)) = true := by native_decide
example : choices.all (fun choice =>
    (program.authorize choice.root
      [GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline, deployRequest choice] entities).toOption.map (·.responses) == (model.compile choice.root).toOption.map (fun policies =>
        [isAuthorized (GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline) entities policies,
         isAuthorized (deployRequest choice) entities policies])) = true := by native_decide

example : [Root.ready, .incident, .recovered].all (fun root =>
    (publish root).toOption.map (fun p => p.json.compress) ==
      (PolicyJson.publish model root.name schema).toOption.map (fun p => p.json.compress)) = true := by
  native_decide

def ready : Choice := { name := "ready", expectedPromotion := true, expectedDeployment := true }
example : admitted { ready with releaseReceiptVerified := false } = false ∧
    promotionAllowed { ready with releaseReceiptVerified := false } = true := by native_decide
example : admitted { ready with pipeline := { cacheIsolated := false } } = false := by native_decide
example : (program.authorize ready.root
    [GoogleThreatCase.request GoogleThreatCase.candidate ready.pipeline,
      { deployRequest ready with context := Cedar.Data.Map.empty }] entities).toOption.map (·.allowed) =
    some false := by native_decide
end Deployment

namespace Sdp
open CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease CedarPooSpec.Cloud.Pipeline
example : choices.all (fun choice =>
    admitted choice == (pipelineAllowed choice && transformAllowed choice)) = true := by native_decide
example : choices.all (fun choice =>
    (program.authorize choice.root
      [GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline, transformRequest choice] entities).toOption.map (·.responses) == (model.compile choice.root).toOption.map (fun policies =>
        [isAuthorized (GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline) entities policies,
         isAuthorized (transformRequest choice) entities policies])) = true := by native_decide

def ready : Choice :=
  { name := "ready", root := "CustomerDataRelease",
    expectedPipeline := true, expectedTransform := true }
example : admitted { ready with keyAuthorized := false } = false ∧
    pipelineAllowed { ready with keyAuthorized := false } = true := by native_decide
example : admitted { ready with pipeline := { cacheIsolated := false } } = false ∧
    transformAllowed { ready with pipeline := { cacheIsolated := false } } = true := by native_decide
example : (program.authorize ready.root
    [GoogleThreatCase.request GoogleThreatCase.candidate ready.pipeline,
      { transformRequest ready with context := Cedar.Data.Map.empty }] entities).toOption.map (·.allowed) =
    some false := by native_decide
end Sdp

namespace Pseudonymization
open CedarPooSpec.PseudonymizationExample
example : cases.all (fun (_, root, req, _) =>
    (program.authorize root [req] entities).toOption.map (·.responses) ==
      (model.compile root).toOption.map (fun policies => [isAuthorized req entities policies])) = true := by
  native_decide
example : PseudonymizationExport.deployableRoots.all (fun root =>
    (Deployment.publish root).toOption.map (fun p => p.json.compress) ==
      (PolicyJson.publish model root.name schema).toOption.map (fun p => p.json.compress)) = true := by
  native_decide
end Pseudonymization

namespace Lifecycle
open CedarPooSpec.PseudonymizationExample.Lifecycle
-- Test-only structural equality compares the complete modeled state.
deriving instance BEq for State

def states : List State := [initial, revoke initial,
  { initial with policyRevision := 1 }, { initial with now := 100 },
  { initial with releaseBudget := 0 }, { initial with ownerApproved := false },
  { initial with authorizedKeys := [] }, { initial with auditAvailable := false },
  { initial with usedIvs := [gcmEffect.iv] }, { initial with approvals := [] }]
def effects : List CedarPooSpec.PseudonymizationExample.Lifecycle.Effect :=
  [ingestEffect, joinEffect, releaseEffect, revealEffect, gcmEffect,
    { gcmEffect with iv := "" }, { releaseEffect with payloadDigest := "" }]

example : states.all (fun state => effects.all fun effect =>
    allowed state effect == Reference.Lifecycle.allowed state effect &&
      prepare state effect == Reference.Lifecycle.prepare state effect) = true := by native_decide
example : effects.all (fun proposal =>
    match Reference.Lifecycle.prepare initial proposal with
    | none => true
    | some ticket => states.all fun state => effects.all fun actual =>
        redeem state ticket actual == Reference.Lifecycle.redeem state ticket actual) = true := by native_decide
end Lifecycle

open Lean in
run_cmd do
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  let declaration := ``CedarPooSpec.Functional.Ready.allowed_pair
  let dependencies ← collectAxioms declaration
  for dependency in dependencies do
    unless allowed.contains dependency.toString do
      throwError "Functional paired admission axiom boundary changed: {dependency}"
  logInfo "FUNCTIONAL-CEDAR-PAIR-AXIOMS-OK universal two-stage admission"

end CedarPooSpec.ExtendedCoverageTest
