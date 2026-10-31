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

def entries : List (String × (Unit → Except String Transport.Entry)) := [
  ("claim-settlement-claims", fun _ => (AWS.ClaimSettlementExport.claimsManifest).map Transport.Entry.manifest),
  ("claim-settlement-banking", fun _ => (AWS.ClaimSettlementExport.bankingManifest).map Transport.Entry.manifest),
  ("claim-settlement-handoff", fun _ => (AWS.ClaimSettlementExport.handoffs).map Transport.Entry.data),
  ("ticket-sharing", fun _ => (TicketSharingExport.manifest).map Transport.Entry.manifest),
  ("clinical", fun _ => (ClinicalBreakGlassExport.manifest).map Transport.Entry.manifest),
  ("pseudonymization-validated", fun _ => (PseudonymizationExport.manifest).map Transport.Entry.manifest),
  ("pseudonymization-deployable", fun _ => (PseudonymizationExport.deploymentManifest).map Transport.Entry.artifacts),
  ("pseudonymization-tabular", fun _ => (PseudonymizationExample.Tabular.fixture).map Transport.Entry.data),
  ("agentic-ai-language-model-health-disclosure", fun _ =>
    (AgenticAI.LanguageModel.DisclosureExport.manifest).map Transport.Entry.manifest),
  ("wearable-triage", fun _ => (WearableTriageExport.manifest).map Transport.Entry.manifest),
  ("model-stewardship", fun _ => (ModelStewardshipExample.ReplayExport.manifest).map Transport.Entry.manifest),
  ("prior-authorization-validated", fun _ => (PriorAuthorizationValidatedExport.manifest).map Transport.Entry.manifest),
  ("prior-authorization-malformed", fun _ => (PriorAuthorizationValidatedExport.malformedManifest).map Transport.Entry.manifest),
  ("prior-authorization-internal-channels", fun _ => (PriorAuthorizationInternalChannelsExport.manifest).map Transport.Entry.manifest),
  ("my-health-record-consumer-platform", fun _ => (MyHealthRecordExample.ValidatedExport.manifest).map Transport.Entry.manifest),
  ("australian-emr-upload", fun _ => (AustralianEMRExample.ValidatedExport.manifest).map Transport.Entry.manifest),
  ("united-states-payer-exchange", fun _ => (UnitedStatesPayerExample.ValidatedExport.manifest).map Transport.Entry.manifest),
  ("attested", fun _ => (AttestedDataAccessExport.manifest).map Transport.Entry.manifest),
  ("attested-views-validated", fun _ => (AttestedViewsValidatedExport.manifest).map Transport.Entry.manifest),
  ("attested-schema-evolution", fun _ => AttestedSchemaEvolutionExport.bundle),
  ("scope-pattern", fun _ => (ScopeAndPatternExport.manifest).map Transport.Entry.manifest),
  ("scope-pattern-validated", fun _ => (ScopeAndPatternValidatedExport.manifest).map Transport.Entry.manifest),
  ("namespaced-enum-validated", fun _ => (NamespacedEnumValidatedExport.manifest).map Transport.Entry.manifest),
  ("network", fun _ => (TrustedNetworkDataAccessExport.manifest).map Transport.Entry.manifest),
  ("network-validated", fun _ => (TrustedNetworkValidatedExport.manifest).map Transport.Entry.manifest),
  ("country-approval", fun _ => (CountryApprovalExport.manifest).map Transport.Entry.manifest),
  ("country-approval-validated", fun _ => (CountryApprovalValidatedExport.manifest).map Transport.Entry.manifest),
  ("purchase-approval", fun _ => (PurchaseApprovalExport.manifest).map Transport.Entry.manifest),
  ("delegated-approval", fun _ => (DelegatedApprovalExport.manifest).map Transport.Entry.manifest),
  ("delegated-matrix", fun _ => (DelegatedApprovalMatrixExport.manifest).map Transport.Entry.manifest),
  ("payment-release", fun _ => (PaymentReleaseExport.manifest).map Transport.Entry.manifest),
  ("agent-delegation", fun _ => (AgentDelegationExport.manifest).map Transport.Entry.manifest),
  ("agent-chain", fun _ => (AgentChainExport.manifest).map Transport.Entry.manifest),
  ("agent-payment", fun _ => (AgentPaymentExport.manifest).map Transport.Entry.manifest),
  ("agent-payment-validated", fun _ => (AgentPaymentValidatedExport.manifest).map Transport.Entry.manifest),
  ("agent-data-flow", fun _ => (AgentDataFlowExport.manifest).map Transport.Entry.manifest),
  ("agent-data-flow-validated", fun _ => (AgentDataFlowValidatedExport.manifest).map Transport.Entry.manifest),
  ("lakehouse-gateway-validated", fun _ => (LakehouseGatewayValidatedExport.manifest).map Transport.Entry.manifest),
  ("multi-account-banking-validated", fun _ => (MultiAccountBankingValidatedExport.manifest).map Transport.Entry.manifest),
  ("reconciliation-validated", fun _ => (CedarPooSpec.AWS.Reconciliation.ValidatedExport.manifest).map Transport.Entry.manifest),
  ("expense-governance-validated", fun _ => (CedarPooSpec.AWS.Expense.ValidatedExport.manifest).map Transport.Entry.manifest),
  ("bounded-session", fun _ => (BoundedSessionExport.manifest).map Transport.Entry.manifest),
  ("shared-budget", fun _ => (SharedBudgetExport.manifest).map Transport.Entry.manifest),
  ("cross-agent-egress-validated", fun _ => (CrossAgentEgressValidatedExport.manifest).map Transport.Entry.manifest),
  ("department-synthesis-validated", fun _ => (DepartmentSynthesisValidatedExport.manifest).map Transport.Entry.manifest),
  ("source-custody-validated", fun _ => (SourceCustodyValidatedExport.manifest).map Transport.Entry.manifest),
  ("supplier-transition", fun _ => (SupplierTransitionExport.manifest).map Transport.Entry.manifest),
  ("vla-command", fun _ => (VlaCommandBoundaryExport.manifest).map Transport.Entry.manifest),
  ("mission-successor", fun _ => (SuccessorBoundaryExport.manifest).map Transport.Entry.manifest),
  ("extension-coverage", fun _ => (ExtensionCoverageExport.manifest).map Transport.Entry.manifest),
  ("tenant-device", fun _ => (TenantDevicePolicyEvolutionExport.manifest).map Transport.Entry.manifest)]

def evaluate {α : Type} (produce : Unit → Except String α) : IO α :=
  match produce () with
  | .ok json => pure json
  | .error message => throw (IO.userError message)

/-- Keep compression inside the IO span: pure let bindings may be sunk past clocks. -/
@[noinline] private def serialize (json : Transport.EncodedJson) : IO String := pure json.wire

@[noinline] private def prepareSources (outputs : List (String × (Unit → Except String Transport.Entry))) :
    IO Transport.EncodedJson :=
  evaluate (fun _ => Transport.prepareCatalogFrom outputs)

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
      -- Factories are consumed one at a time; no complete raw catalog is retained.
      let encoded ← prepareSources selected
      phase started "sources-ready"
      let text ← serialize encoded
      phase started "serialized"
      IO.println text
      phase started "output-written"
  | ["all"] => do
      let outputs ← entries.mapM fun (name, produce) => do
        let json ← evaluate (fun _ => do (← produce ()).toJson)
        pure (name, json)
      for (name, json) in outputs do
        IO.FS.writeFile s!".lake/build/{name}-manifest.json" json.compress
  | [name] =>
      match entries.find? (fun entry => entry.1 == name) with
      | some (_, produce) => do
          let json ← evaluate (fun _ => do (← produce ()).toJson)
          IO.println json.compress
      | none => throw (IO.userError s!"unknown manifest: {name}")
  | _ => throw (IO.userError "expected a manifest name or all")

end CedarPooSpec.Manifests
