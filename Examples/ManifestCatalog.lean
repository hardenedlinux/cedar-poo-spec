import CedarPooSpec.Transport.SourceCatalog
import Examples.Enterprise.AWS.FinancialServices.ClaimSettlementExport
import Examples.Governance.TicketSharingExport
import Examples.Health.ClinicalBreakGlassExport
import Examples.Health.PseudonymizationExport
import Examples.Health.Pseudonymization.Tabular
import Examples.Health.AgenticAI.LanguageModel.DisclosureExport
import Examples.Health.WearableTriageExport
import Examples.Health.ModelStewardship.ReplayExport
import Examples.Health.PriorAuthorization.ValidatedExport
import Examples.Health.PriorAuthorization.InternalChannelsExport
import Examples.Health.MyHealthRecord.ValidatedExport
import Examples.Health.Interoperability.ValidatedExport
import Examples.Health.Interoperability.UnitedStatesExport
import Examples.Governance.AttestedDataAccessExport
import Examples.Governance.AttestedViewsValidatedExport
import Examples.Governance.AttestedSchemaEvolutionExport
import Examples.Language.ScopeAndPatternExport
import Examples.Language.ScopeAndPatternValidatedExport
import Examples.Language.NamespacedEnumValidatedExport
import Examples.Governance.TrustedNetworkDataAccessExport
import Examples.Governance.TrustedNetworkValidatedExport
import Examples.Governance.CountryApprovalExport
import Examples.Governance.CountryApprovalValidatedExport
import Examples.Enterprise.Procurement.PurchaseApprovalExport
import Examples.Enterprise.Procurement.DelegatedApprovalExport
import Examples.Enterprise.Procurement.DelegatedApprovalMatrixExport
import Examples.Enterprise.Payment.PaymentReleaseExport
import Examples.Enterprise.Agent.Delegation.AgentDelegationExport
import Examples.Enterprise.Agent.Chain.AgentChainExport
import Examples.Enterprise.Agent.Payment.AgentPaymentExport
import Examples.Enterprise.Agent.Payment.ValidatedExport
import Examples.Enterprise.Agent.DataFlow.AgentDataFlowExport
import Examples.Enterprise.Agent.DataFlow.ValidatedExport
import Examples.Enterprise.AWS.FinancialServices.LakehouseGateway.ValidatedExport
import Examples.Enterprise.AWS.FinancialServices.MultiAccountBanking.ValidatedExport
import Examples.Enterprise.AWS.FinancialServices.Reconciliation.ValidatedExport
import Examples.Enterprise.AWS.AgenticPlatform.Expense.ValidatedExport
import Examples.Enterprise.Agent.Session.BoundedSessionExport
import Examples.Enterprise.Agent.Fanout.SharedBudgetExport
import Examples.Enterprise.Agent.Fanout.CrossAgentEgressValidatedExport
import Examples.Enterprise.Agent.Department.ValidatedExport
import Examples.Enterprise.Personnel.ValidatedExport
import Examples.Enterprise.Vehicle.Uptane.SupplierTransitionExport
import Examples.Enterprise.Vehicle.VLA.CommandBoundaryExport
import Examples.Enterprise.Vehicle.Mission.SuccessorBoundaryExport
import Examples.Language.ExtensionCoverageExport
import Examples.Scenarios.TenantDevicePolicyEvolutionExport

/-! Evaluate the same pure manifest definitions in one Lean process. -/

namespace CedarPooSpec.Manifests

def entries : List (String × (Unit → Except String Lean.Json)) := [
  ("claim-settlement-claims", fun _ => AWS.ClaimSettlementExport.claimsManifest),
  ("claim-settlement-banking", fun _ => AWS.ClaimSettlementExport.bankingManifest),
  ("claim-settlement-handoff", fun _ => AWS.ClaimSettlementExport.handoffs),
  ("ticket-sharing", fun _ => TicketSharingExport.manifest),
  ("clinical", fun _ => ClinicalBreakGlassExport.manifest),
  ("pseudonymization-validated", fun _ => PseudonymizationExport.manifest),
  ("pseudonymization-deployable", fun _ => PseudonymizationExport.deploymentManifest),
  ("pseudonymization-tabular", fun _ => PseudonymizationExample.Tabular.fixture),
  ("agentic-ai-language-model-health-disclosure", fun _ =>
    AgenticAI.LanguageModel.DisclosureExport.manifest),
  ("wearable-triage", fun _ => WearableTriageExport.manifest),
  ("model-stewardship", fun _ => ModelStewardshipExample.ReplayExport.manifest),
  ("prior-authorization-validated", fun _ => PriorAuthorizationValidatedExport.manifest),
  ("prior-authorization-malformed", fun _ => PriorAuthorizationValidatedExport.malformedManifest),
  ("prior-authorization-internal-channels", fun _ => PriorAuthorizationInternalChannelsExport.manifest),
  ("my-health-record-consumer-platform", fun _ => MyHealthRecordExample.ValidatedExport.manifest),
  ("australian-emr-upload", fun _ => AustralianEMRExample.ValidatedExport.manifest),
  ("united-states-payer-exchange", fun _ => UnitedStatesPayerExample.ValidatedExport.manifest),
  ("attested", fun _ => AttestedDataAccessExport.manifest),
  ("attested-views-validated", fun _ => AttestedViewsValidatedExport.manifest),
  ("attested-schema-evolution", fun _ => AttestedSchemaEvolutionExport.bundle),
  ("scope-pattern", fun _ => ScopeAndPatternExport.manifest),
  ("scope-pattern-validated", fun _ => ScopeAndPatternValidatedExport.manifest),
  ("namespaced-enum-validated", fun _ => NamespacedEnumValidatedExport.manifest),
  ("network", fun _ => TrustedNetworkDataAccessExport.manifest),
  ("network-validated", fun _ => TrustedNetworkValidatedExport.manifest),
  ("country-approval", fun _ => CountryApprovalExport.manifest),
  ("country-approval-validated", fun _ => CountryApprovalValidatedExport.manifest),
  ("purchase-approval", fun _ => PurchaseApprovalExport.manifest),
  ("delegated-approval", fun _ => DelegatedApprovalExport.manifest),
  ("delegated-matrix", fun _ => DelegatedApprovalMatrixExport.manifest),
  ("payment-release", fun _ => PaymentReleaseExport.manifest),
  ("agent-delegation", fun _ => AgentDelegationExport.manifest),
  ("agent-chain", fun _ => AgentChainExport.manifest),
  ("agent-payment", fun _ => AgentPaymentExport.manifest),
  ("agent-payment-validated", fun _ => AgentPaymentValidatedExport.manifest),
  ("agent-data-flow", fun _ => AgentDataFlowExport.manifest),
  ("agent-data-flow-validated", fun _ => AgentDataFlowValidatedExport.manifest),
  ("lakehouse-gateway-validated", fun _ => LakehouseGatewayValidatedExport.manifest),
  ("multi-account-banking-validated", fun _ => MultiAccountBankingValidatedExport.manifest),
  ("reconciliation-validated", fun _ => CedarPooSpec.AWS.Reconciliation.ValidatedExport.manifest),
  ("expense-governance-validated", fun _ => CedarPooSpec.AWS.Expense.ValidatedExport.manifest),
  ("bounded-session", fun _ => BoundedSessionExport.manifest),
  ("shared-budget", fun _ => SharedBudgetExport.manifest),
  ("cross-agent-egress-validated", fun _ => CrossAgentEgressValidatedExport.manifest),
  ("department-synthesis-validated", fun _ => DepartmentSynthesisValidatedExport.manifest),
  ("source-custody-validated", fun _ => SourceCustodyValidatedExport.manifest),
  ("supplier-transition", fun _ => SupplierTransitionExport.manifest),
  ("vla-command", fun _ => VlaCommandBoundaryExport.manifest),
  ("mission-successor", fun _ => SuccessorBoundaryExport.manifest),
  ("extension-coverage", fun _ => ExtensionCoverageExport.manifest),
  ("tenant-device", fun _ => TenantDevicePolicyEvolutionExport.manifest)]

def evaluate (produce : Unit → Except String Lean.Json) : IO Lean.Json :=
  match produce () with
  | .ok json => pure json
  | .error message => throw (IO.userError message)

/-- Keep compression inside the IO span: pure let bindings may be sunk past clocks. -/
@[noinline] private def serialize (json : Lean.Json) : IO String := pure json.compress

@[noinline] private def prepareSources (outputs : List (String × Lean.Json)) : IO Lean.Json :=
  evaluate (fun _ => Transport.sourceCatalog outputs)

private def phase (started : Option Nat) (name : String) : IO Unit := do
  if let some start := started then
    let elapsed := (← IO.monoNanosNow) - start
    (← IO.getStderr).putStrLn (Lean.Json.mkObj [
      ("observation", Lean.toJson "native-phase"), ("phase", Lean.toJson name),
      ("elapsed_ns", Lean.toJson elapsed)]).compress

def run (args : List String) (observe : Bool := false) : IO Unit := do
  let started ← if observe then pure (some (← IO.monoNanosNow)) else pure none
  match args with
  | "catalog" :: requested => do
      for name in requested do
        unless entries.any (fun entry => entry.1 == name) do
          throw (IO.userError s!"unknown manifest: {name}")
      let selected := if requested.isEmpty then entries else
        entries.filter (fun entry => requested.contains entry.1)
      let outputs ← selected.mapM fun (name, produce) => do
        let json ← evaluate produce
        pure (name, json)
      phase started "catalog-ready"
      let encoded ← prepareSources outputs
      phase started "sources-ready"
      let text ← serialize encoded
      phase started "serialized"
      IO.println text
      phase started "output-written"
  | ["all"] => do
      let outputs ← entries.mapM fun (name, produce) => do
        let json ← evaluate produce
        pure (name, json)
      for (name, json) in outputs do
        IO.FS.writeFile s!".lake/build/{name}-manifest.json" json.compress
  | [name] =>
      match entries.find? (fun entry => entry.1 == name) with
      | some (_, produce) => do
          let json ← evaluate produce
          IO.println json.compress
      | none => throw (IO.userError s!"unknown manifest: {name}")
  | _ => throw (IO.userError "expected a manifest name or all")

end CedarPooSpec.Manifests
