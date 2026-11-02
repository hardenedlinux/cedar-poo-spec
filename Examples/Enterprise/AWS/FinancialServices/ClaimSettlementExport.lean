import Examples.Enterprise.AWS.FinancialServices.ClaimSettlementHandoff
import CedarPooSpec.SchemaJson

/-! Independent schema-bearing claim and banking requests plus simulated
handoff scope. No credential issuance or completed settlement is asserted. -/
namespace CedarPooSpec.AWS.ClaimSettlementExport
open Cedar.Spec CedarPooSpec.Admission CedarPooSpec.AWS.ClaimSettlementHandoff
open CedarPooSpec.AWS.ClaimSettlement

structure Scenario where
  name : String
  selection : Selection
  profile : Handoff.Object := caseProfile
  handoff : Handoff.Grant := grant

def invalidProfile : Handoff.Object :=
  (Handoff.onCase caseProfile "InvalidCase" "" "").toOption.get (by native_decide)

def scenarios : List Scenario := [
  { name := "ready", selection := selected },
  { name := "bank-paused", selection := { selected with bankRoot := "TransferPaused" } },
  { name := "claims-eu", selection := { selected with geography := some "EU" } },
  { name := "claims-missing-geography", selection := { selected with geography := none } },
  { name := "source-gap-diagnostic", selection := { selected with claimRoot := "SourceCombined", geography := none } },
  { name := "wrong-case", selection := { selected with caseId := "other-case" } },
  { name := "wrong-digest", selection := { selected with claimDigest := "other-digest" } },
  { name := "wrong-actor", selection := { selected with actors :=
      { sampleActors with bankOperator := CedarPooSpec.MultiAccountBankingExample.colleague } } },
  { name := "stale-epoch", selection := { selected with currentEpoch := 8 } },
  { name := "expired", selection := { selected with now := 20 } },
  { name := "other-mode", selection := { selected with mode := "OBO" } },
  { name := "gateway-bound-mode", selection := { selected with mode := "GatewayBoundM2M" } },
  { name := "unknown-mode", selection := { selected with mode := "unknown" } },
  { name := "invalid-profile", selection := selected, profile := invalidProfile }]

def claimRequests (selection : Selection) : List Request :=
  [CedarPooSpec.LakehouseGatewayExample.queryClaims,
    CedarPooSpec.LakehouseGatewayExample.claimDetails].map fun action =>
      CedarPooSpec.LakehouseGatewayExample.request selection.actors.adjuster action selection.geography

def bankCalls (selection : Selection) :=
  CedarPooSpec.MultiAccountBankingLineage.transferRoute.map fun call =>
    { call with origin := selection.actors.bankOperator }

def claimsManifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.LakehouseGatewayExample.model CedarPooSpec.LakehouseGatewayExample.schema :=
      CedarPooSpec.LakehouseGatewayExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let batches ← LeanPoo.Functional.Validation.traverse (fun scenario =>
    LeanPoo.Functional.Validation.traverse (fun (request, index) =>
      owner.case
        s!"{scenario.name}-claims-{index}" scenario.selection.claimRoot scenario.selection.claimRoot
        request CedarPooSpec.LakehouseGatewayExample.entities)
      (claimRequests scenario.selection).zipIdx) scenarios
  SchemaJson.manifest CedarPooSpec.LakehouseGatewayExample.schema batches.flatten

def bankingManifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let batches ← LeanPoo.Functional.Validation.traverse (fun scenario =>
    LeanPoo.Functional.Validation.traverse (fun (call, index) =>
      owner.case
        s!"{scenario.name}-bank-{index}" scenario.selection.bankRoot scenario.selection.bankRoot
        (CedarPooSpec.MultiAccountBankingExample.request call.origin call.action)
        CedarPooSpec.MultiAccountBankingExample.entities)
      (bankCalls scenario.selection).zipIdx) scenarios
  SchemaJson.manifest CedarPooSpec.MultiAccountBankingExample.schema batches.flatten

def scopeJson (scope : Handoff.Scope) : Lean.Json := Lean.Json.mkObj [
  ("caseId", Lean.toJson scope.caseId), ("claimDigest", Lean.toJson scope.claimDigest),
  ("sourceActor", Lean.toJson (toString scope.sourceActor)),
  ("targetActor", Lean.toJson (toString scope.targetActor)),
  ("sourceRoot", Lean.toJson scope.sourceRoot), ("targetRoot", Lean.toJson scope.targetRoot),
  ("credentialMode", Lean.toJson scope.credentialMode)]

def requirementName : CedarPooSpec.MultiAccountBankingLineage.Requirement → String
  | .userJwtAgentToGateway => "userJwtAgentToGateway"
  | .cedarAtGateway => "cedarAtGateway"
  | .m2mGatewayToLob => "m2mGatewayToLob"
  | .jwtAtLob => "jwtAtLob"
  | .gatewayInWorkloadChain => "gatewayInWorkloadChain"
  | .oboGatewayToLob => "oboGatewayToLob"
  | .userAtLob => "userAtLob"
  | .retailDataPlane => "retailDataPlane"
  | .transactionDataPlane => "transactionDataPlane"
  | .lendingDataPlane => "lendingDataPlane"

def handoffs
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.LakehouseGatewayExample.model CedarPooSpec.LakehouseGatewayExample.schema × CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      (CedarPooSpec.LakehouseGatewayExample.program, CedarPooSpec.MultiAccountBankingExample.program)) : Except String Lean.Json := do
  return Lean.toJson (scenarios.map fun scenario =>
    let selection := scenario.selection
    Lean.Json.mkObj [
      ("name", Lean.toJson scenario.name),
      ("scope", scopeJson selection.scope),
      ("configured", match Handoff.scope? scenario.profile with
        | none => Lean.Json.null | some scope => scopeJson scope),
      ("grant", Lean.Json.mkObj [("scope", scopeJson scenario.handoff.scope),
        ("epoch", Lean.toJson scenario.handoff.epoch), ("expiresAt", Lean.toJson scenario.handoff.expiresAt)]),
      ("currentEpoch", Lean.toJson selection.currentEpoch), ("now", Lean.toJson selection.now),
      ("claims", Lean.toJson ((claimRequests selection).zipIdx.map fun (_, index) =>
        s!"{scenario.name}-claims-{index}")),
      ("banking", Lean.toJson ((bankCalls selection).zipIdx.map fun (call, index) =>
        Lean.Json.mkObj [("caseName", Lean.toJson s!"{scenario.name}-bank-{index}"),
          ("phase", Lean.toJson call.phase), ("lob", Lean.toJson call.lob),
          ("origin", Lean.toJson (toString call.origin)), ("action", Lean.toJson (toString call.action)),
          ("required", match CedarPooSpec.MultiAccountBankingLineage.requirements selection.mode call.lob with
            | none => Lean.Json.null | some required => Lean.toJson (required.map requirementName))])),
      ("expectedGateway", Lean.toJson ((gatewayPlanAllows (programContext := (programContext.1, programContext.2))) selection.claimRoot selection.bankRoot
        selection.mode selection.actors selection.geography)),
      ("expectedAdmitted", Lean.toJson (admitted scenario.profile scenario.handoff selection))])
end CedarPooSpec.AWS.ClaimSettlementExport
