import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Platform.AWS.AgentCore.Gateway
import CedarPooSpec.Data.Lakehouse.LocationBoundary
import CedarPooSpec.Data.Lakehouse.LocationProfile
import CedarPooSpec.Vertical.FinancialServices.ClaimSummaryVeto
import CedarPooSpec.Revision

/-! A Cedar projection of the AWS AgentCore lakehouse Policy + Interceptor
example. The interceptor, token exchange, and Lake Formation checks remain
external authorities. The source gives the role, EU, and restricted-region
forbids; the final unresolved-geography veto is a locally proposed hardening. -/

namespace CedarPooSpec.LakehouseGatewayExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Platform.AWS.AgentCore
open CedarPooSpec.Data.Lakehouse
open CedarPooSpec.Vertical.FinancialServices

def policyholderUS : EntityUID := user "policyholder001"
def policyholderEU : EntityUID := user "policyholder002"
def adjusterUS : EntityUID := user "adjuster001"
def adjusterEU : EntityUID := user "adjuster002"
def gateway : EntityUID := CedarPooSpec.Platform.AWS.AgentCore.gateway "lakehouse-gateway"
def queryClaims : EntityUID :=
  action "lakehouse-mcp-target___query_claims"
def claimDetails : EntityUID :=
  action "lakehouse-mcp-target___get_claim_details"
def claimsSummary : EntityUID :=
  action "lakehouse-mcp-target___get_claims_summary"
def loginAudit : EntityUID :=
  action "lakehouse-mcp-target___query_login_audit"
def textToSql : EntityUID :=
  action "lakehouse-mcp-target___text_to_sql"

def tools : List EntityUID :=
  [queryClaims, claimDetails, claimsSummary, loginAudit, textToSql]

def inputType : RecordType := Map.make [("geography", .optional .string)]
def actionEntry : ActionSchemaEntry :=
  CedarPooSpec.Platform.AWS.AgentCore.actionEntry
    (Map.make [("input", .required (.record inputType))])
def schema : Schema :=
  ⟨Map.make [
    (userType, .standard ⟨Set.empty, Map.empty, some .string⟩),
    (gatewayType, .standard ⟨Set.empty, Map.empty, none⟩)],
    Map.make (tools.map (·, actionEntry))⟩

def data (tags : List (String × Value) := []) : EntityData := entityData tags
def entities : Entities := Map.make (
  [(policyholderUS, data [("cognito:groups", .prim (.string "policyholders"))]),
   (policyholderEU, data [("cognito:groups", .prim (.string "policyholders"))]),
   (adjusterUS, data [("cognito:groups", .prim (.string "adjusters"))]),
   (adjusterEU, data [("cognito:groups", .prim (.string "adjusters"))]),
   (gateway, data)] ++ tools.map (·, data))

def request (user action : EntityUID) (geography : Option String) : Request :=
  let attrs := geography.toList.map fun location =>
    ("geography", Value.prim (.string location))
  ⟨user, action, gateway,
    Map.make [("input", .record (Map.make attrs))]⟩

def groups : Expr :=
  .binaryApp .getTag (.var .principal) (.lit (.string "cognito:groups"))
def hasGroups : Expr :=
  .binaryApp .hasTag (.var .principal) (.lit (.string "cognito:groups"))
def policyholderPattern : Pattern :=
  [.star, .justChar 'p', .justChar 'o', .justChar 'l', .justChar 'i',
   .justChar 'c', .justChar 'y', .justChar 'h', .justChar 'o',
   .justChar 'l', .justChar 'd', .justChar 'e', .justChar 'r',
   .justChar 's', .star]
def isPolicyholder : Expr :=
  .and hasGroups (.unaryApp (.like policyholderPattern) groups)

def baselinePermit : Policy :=
  scopedPolicy "gateway-baseline" .permit gateway (.actionScope .any)
def summaryControl : ClaimSummaryVeto :=
  { policyId := "policyholder-summary",
    principalScope := .principalScope (.is userType),
    summaryAction := claimsSummary,
    resourceScope := .resourceScope (.eq gateway),
    policyholderCondition := isPolicyholder }
def euTemplate : LocationBoundary :=
  { policyId := "eu-individual-claims",
    principalScope := .principalScope (.is userType),
    actionScope := .actionInAny [queryClaims, claimDetails],
    resourceScope := .resourceScope (.eq gateway),
    deniedLocation := "EU" }

def euProfile : LocationProfile.Object :=
  (LocationProfile.define "EUProfile" euTemplate).toOption.get
    (by native_decide)

def restrictedProfile : LocationProfile.Object :=
  (euProfile.extendWith "RestrictedProfile" do
    LeanPoo.Object.Dataflow.Builder.value .policyId "restricted-geography"
    LeanPoo.Object.Dataflow.Builder.value .actionScope (.actionInAny tools)
    LeanPoo.Object.Dataflow.Builder.value .location "RESTRICTED")
    |>.toOption.get (by native_decide)

def euControl : LocationBoundary :=
  (LocationProfile.boundary? euProfile).get (by native_decide)
def restrictedControl : LocationBoundary :=
  (LocationProfile.boundary? restrictedProfile).get (by native_decide)

/-- A proposed extension: deny calls when geography is absent or the sample
    interceptor's `UNKNOWN` fallback is used. Neither matches the source's
    EU or RESTRICTED rules. -/
def unresolvedProfile : LocationProfile.Object :=
  (restrictedProfile.extendWith "UnresolvedProfile" do
    LeanPoo.Object.Dataflow.Builder.value .policyId "unresolved-geography"
    LeanPoo.Object.Dataflow.Builder.value .location "UNKNOWN"
    LeanPoo.Object.Dataflow.Builder.value .denyMissing true)
    |>.toOption.get (by native_decide)

def unresolvedControl : LocationBoundary :=
  (LocationProfile.boundary? unresolvedProfile).get (by native_decide)
def unresolvedGeographyVeto : Policy := unresolvedControl.policy

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "GatewayBase", edits := [.extend baselinePermit] }] }
  let role ← base.extend "Role" "GatewayBase" [summaryControl.introduce]
  let eu ← role.extend "EU" "GatewayBase" [euControl.introduce]
  let restricted ← eu.extend "Restricted" "GatewayBase" [restrictedControl.introduce]
  let combined ← restricted.mix "SourceCombined" ["Role", "EU", "Restricted"]
  combined.extend "FailClosed" "SourceCombined" [unresolvedControl.introduce]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

def sourceCases : List (String × EntityUID × EntityUID × Option String × Decision) := [
  ("policyholder-us-query", policyholderUS, queryClaims, some "US", .allow),
  ("policyholder-eu-query", policyholderEU, queryClaims, some "EU", .deny),
  ("policyholder-eu-summary", policyholderEU, claimsSummary, some "EU", .deny),
  ("adjuster-us-summary", adjusterUS, claimsSummary, some "US", .allow),
  ("adjuster-eu-details", adjusterEU, claimDetails, some "EU", .deny),
  ("restricted-tool", adjusterUS, loginAudit, some "RESTRICTED", .deny)]

def decideAt
     (root : String) (req : Request)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.LakehouseGatewayExample.model CedarPooSpec.LakehouseGatewayExample.schema :=
      CedarPooSpec.LakehouseGatewayExample.program) : Option Decision := do
  let response ← (programContext.response root req entities).toOption
  if response.erroringPolicies.isEmpty then some response.decision else none

theorem sourceDecisionsExact :
    sourceCases.all (fun (_, user, action, location, expected) =>
      decideAt "SourceCombined" (request user action location) == some expected) = true := by
  native_decide

/-- Neither individual owner catches both independent restrictions. -/
theorem ownerBranchesNeedComposition :
    decideAt "Role" (request policyholderEU queryClaims (some "EU")) = some .allow ∧
    decideAt "EU" (request policyholderEU claimsSummary (some "EU")) = some .allow ∧
    decideAt "Restricted" (request policyholderEU claimsSummary (some "EU")) = some .allow := by
  native_decide

theorem unresolvedGeographyGapAndExtension :
    decideAt "SourceCombined" (request adjusterUS queryClaims none) = some .allow ∧
    decideAt "FailClosed" (request adjusterUS queryClaims none) = some .deny ∧
    decideAt "SourceCombined" (request adjusterUS queryClaims (some "UNKNOWN")) = some .allow ∧
    decideAt "FailClosed" (request adjusterUS queryClaims (some "UNKNOWN")) = some .deny ∧
    sourceCases.all (fun (_, user, action, location, expected) =>
      decideAt "FailClosed" (request user action location) == some expected) = true := by
  native_decide

theorem localRevision :
    ((model.compileRevision "SourceCombined" "FailClosed").toOption.get
      (by native_decide)).changedPolicyIds = [unresolvedGeographyVeto.id] := by
  native_decide

theorem oneFreshPolicyBody :
    ((model.compileRevision "SourceCombined" "FailClosed").toOption.get
      (by native_decide)).freshPolicies = [unresolvedGeographyVeto] := by
  native_decide

theorem allRootsValidated :
    ["GatewayBase", "Role", "EU", "Restricted", "SourceCombined",
      "FailClosed"].all (fun root =>
        (CedarPooSpec.LakehouseGatewayExample.program.publish root).isOk) = true := by
  native_decide

end CedarPooSpec.LakehouseGatewayExample
