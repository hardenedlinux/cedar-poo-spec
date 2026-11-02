import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.AWS.FinancialServices.MultiAccountBanking.MultiAccountBanking
import CedarPooSpec.Authorization.Compound
import LeanPoo.C4.Linearize
import LeanPoo.Object.Multimethod

/-! A source-grounded obligation topology for the banking agent's mixed route.
It describes checks at separate authorities; it does not attest that an AWS
deployment performed them. SourceM2M matches the sample's credential mode.
GatewayBoundM2M and OBO are AWS-documented deployment alternatives. -/

namespace CedarPooSpec.MultiAccountBankingLineage

open CedarPooSpec.MultiAccountBankingExample

/-- Each constructor names a relation that must be established by its owner. -/
inductive Requirement where
  | userJwtAgentToGateway
  | cedarAtGateway
  | m2mGatewayToLob
  | jwtAtLob
  | gatewayInWorkloadChain
  | oboGatewayToLob
  | userAtLob
  | retailDataPlane
  | transactionDataPlane
  | lendingDataPlane
  deriving BEq, Repr

def credentialModes : LeanPoo.C4.Graph := { nodes := [
  { name := "Identity" },
  { name := "SourceM2M", parentOrders := [["Identity"]] },
  { name := "GatewayBoundM2M", parentOrders := [["SourceM2M"]] },
  { name := "OBO", parentOrders := [["Identity"]] }] }

def lobClasses : LeanPoo.C4.Graph := { nodes := [
  { name := "LOB" },
  { name := "Retail", parentOrders := [["LOB"]] },
  { name := "Transaction", parentOrders := [["LOB"]] },
  { name := "Lending", parentOrders := [["LOB"]] }] }

private def routeGeneric :
    LeanPoo.Object.Multimethod (List String × List String)
      (List Requirement) (List Requirement) :=
  { arity := 2
    precedence := fun shape => [shape.1, shape.2]
    combine := fun methods _ => methods.toList.flatten }

/-- The mode and LOB axes each contribute checks. A new LOB can add its own
    data-plane relation without copying the identity and Gateway methods. -/
private def registered : Except LeanPoo.Object.MultimethodError
    (LeanPoo.Object.Multimethod (List String × List String)
      (List Requirement) (List Requirement)) := do
  let identity ← routeGeneric.register
    [.prototype "Identity", .any]
    [.userJwtAgentToGateway, .cedarAtGateway]
  let sample ← identity.register
    [.prototype "SourceM2M", .any]
    [.m2mGatewayToLob, .jwtAtLob]
  let bound ← sample.register
    [.prototype "GatewayBoundM2M", .any]
    [.gatewayInWorkloadChain]
  let obo ← bound.register
    [.prototype "OBO", .any]
    [.oboGatewayToLob, .userAtLob, .jwtAtLob]
  let retail ← obo.register [.any, .prototype "Retail"] [.retailDataPlane]
  let transaction ← retail.register [.any, .prototype "Transaction"]
    [.transactionDataPlane]
  transaction.register [.any, .prototype "Lending"] [.lendingDataPlane]

def requirements (mode lob : String) : Option (List Requirement) := do
  let modeOrder ← (LeanPoo.C4.linearize credentialModes mode).toOption
  let lobOrder ← (LeanPoo.C4.linearize lobClasses lob).toOption
  let generic ← registered.toOption
  let (checks, _) ← (generic.call (modeOrder, lobOrder)).toOption
  return checks

/-- A step relates its origin, phase, Gateway action, and owning LOB. -/
structure RouteCall where
  phase : String
  origin : Cedar.Spec.EntityUID
  lob : String
  action : Cedar.Spec.EntityUID

def belongsTo (lob : String) (action : Cedar.Spec.EntityUID) : Bool :=
  match lob with
  | "Retail" => retailTools.contains action
  | "Transaction" => transactionTools.contains action
  | "Lending" => lendingTools.contains action
  | _ => false

/-- These are the four calls specified in the sample agent's transfer prompt.
    Two separate Retail calls debit and credit after Transaction writes its
    Completed payment record. This is an authorization plan, not a transaction. -/
def transferRoute : List RouteCall := [
  ⟨"balance-check", banker, "Retail", balance⟩,
  ⟨"record-transfer", banker, "Transaction", transfer⟩,
  ⟨"debit-source", banker, "Retail", updateBalance⟩,
  ⟨"credit-destination", banker, "Retail", updateBalance⟩]

def routeWellRelated : Bool :=
  transferRoute.all fun call =>
    call.origin == banker && belongsTo call.lob call.action

def gatewayAllowsCalls
     (root : String) (calls : List RouteCall)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) : Bool :=
  if !calls.all (fun call => belongsTo call.lob call.action) then false
  else
    match programContext.authorize
        root (calls.map fun call => request call.origin call.action) entities with
    | .error _ => false
    | .ok receipt => receipt.allowed

def gatewayAllowsRoute
     (root : String)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) : Bool :=
  (gatewayAllowsCalls (programContext := programContext)) root transferRoute

def routeRequirements (mode : String) : Option (List (List Requirement)) :=
  transferRoute.mapM fun call =>
    if belongsTo call.lob call.action then requirements mode call.lob else none

/-- One construction result links the POO dispatch result to the Cedar
    decision for the same origin, action, and LOB. It is a plan, not evidence
    that the outbound credential or business effect occurred. -/
structure PlannedCall where
  call : RouteCall
  required : List Requirement
  gatewayDecision : Cedar.Spec.Decision

def plannedCalls
     (mode root : String) (calls : List RouteCall)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) :
    Option (List PlannedCall) := do
  if !calls.all (fun call => belongsTo call.lob call.action) then none else do
    let receipt ← (programContext.authorize
        root (calls.map fun call => request call.origin call.action) entities).toOption
    if calls.length != receipt.responses.length then none else
      (calls.zip receipt.responses).mapM fun (call, response) => do
        if !response.erroringPolicies.isEmpty then none else do
          let required ← requirements mode call.lob
          return ⟨call, required, response.decision⟩

def plannedCall
     (mode root : String) (call : RouteCall)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) : Option PlannedCall := do
  let calls ← (plannedCalls (programContext := programContext)) mode root [call]
  calls.head?

def plannedRoute
     (mode root : String)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) : Option (List PlannedCall) :=
  (plannedCalls (programContext := programContext)) mode root transferRoute

def plannedRouteAllowed
     (mode root : String)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) : Bool :=
  match (plannedRoute (programContext := programContext)) mode root with
  | none => false
  | some calls => !calls.isEmpty && calls.all fun call =>
      call.gatewayDecision == .allow &&
        call.required.contains .userJwtAgentToGateway &&
        call.required.contains .cedarAtGateway &&
        call.required.contains .jwtAtLob

theorem composedMixedRoutePlan :
    plannedRouteAllowed "SourceM2M" "OwnerCombined" = true ∧
    plannedRouteAllowed "SourceM2M" "Retail" = false ∧
    plannedRouteAllowed "SourceM2M" "Transaction" = false := by
  native_decide

theorem transferRelationExact :
    routeWellRelated = true ∧
    transferRoute.map (·.phase) =
      ["balance-check", "record-transfer", "debit-source", "credit-destination"] := by
  native_decide

/-- The same identity chain specializes into the correct local data-plane
    relation at each hop. A Transaction requirement never substitutes for a
    Retail balance update, even though both use the same Gateway. -/
theorem accountSpecificComposition :
    (match routeRequirements "SourceM2M" with
     | some [balanceChecks, transferChecks, debitChecks, creditChecks] =>
         balanceChecks.contains .retailDataPlane &&
         !balanceChecks.contains .transactionDataPlane &&
         transferChecks.contains .transactionDataPlane &&
         !transferChecks.contains .retailDataPlane &&
         debitChecks.contains .retailDataPlane &&
         creditChecks.contains .retailDataPlane
     | _ => false) = true := by native_decide

theorem sampleGatewayAllowsEachCall :
    gatewayAllowsRoute "SampleBroad" = true ∧
    gatewayAllowsRoute "OwnerCombined" = true := by native_decide

theorem eitherOwnerAloneBreaksRoute :
    gatewayAllowsRoute "Retail" = false ∧
    gatewayAllowsRoute "Transaction" = false := by native_decide

/-- The sample Gateway policy permits the Transaction tool as a standalone
    call. Per-call authorization cannot establish that the later Retail debit
    and credit occurred. The sample tool itself writes a Completed record
    before requesting those later calls from the agent. -/
theorem isolatedTransferIsAuthorized :
    gatewayAllowsCalls "OwnerCombined"
      [⟨"record-transfer", banker, "Transaction", transfer⟩] = true := by
  native_decide

/-- The published M2M sample carries the user JWT to the Gateway but uses
    a separate service credential on every Gateway-to-LOB edge. -/
theorem sourceLineageShape :
    (routeRequirements "SourceM2M").isSome = true ∧
    (routeRequirements "SourceM2M").toList.flatten.all
      (fun checks => checks.contains .userJwtAgentToGateway ∧
        checks.contains .cedarAtGateway ∧
        checks.contains .m2mGatewayToLob ∧
        checks.contains .jwtAtLob ∧
        !checks.contains .userAtLob ∧
        !checks.contains .gatewayInWorkloadChain) = true := by native_decide

/-- The article recommends a Gateway-bound workload configuration in each
    LOB Runtime. It adds one relation for every call without changing LOB
    data-plane ownership or the four Gateway decisions. -/
theorem gatewayBoundAddition :
    (routeRequirements "GatewayBoundM2M").toList.flatten.all
      (fun checks => checks.contains .gatewayInWorkloadChain ∧
        checks.contains .m2mGatewayToLob ∧
        !checks.contains .userAtLob) = true ∧
    gatewayAllowsRoute "OwnerCombined" = true := by native_decide

/-- AWS documents OBO as a different outbound mode. The sample does not use it. -/
theorem oboAlternativeShape :
    (routeRequirements "OBO").toList.flatten.all
      (fun checks => checks.contains .oboGatewayToLob ∧
        checks.contains .userAtLob ∧
        !checks.contains .m2mGatewayToLob) = true := by native_decide

end CedarPooSpec.MultiAccountBankingLineage
