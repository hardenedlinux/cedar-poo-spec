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

def entries : List (String × Transport.EntryProducer) := [
  ("claim-settlement-claims", Transport.EntryProducer.of CedarPooSpec.LakehouseGatewayExample.program (fun owner => ((AWS.ClaimSettlementExport.claimsManifest owner)).map Transport.Entry.manifest)),
  ("claim-settlement-banking", Transport.EntryProducer.of CedarPooSpec.MultiAccountBankingExample.program (fun owner => ((AWS.ClaimSettlementExport.bankingManifest owner)).map Transport.Entry.manifest)),
  ("claim-settlement-handoff", Transport.EntryProducer.of AWS.ClaimSettlementExport.handoffs (fun outcome => outcome.map Transport.Entry.data)),
  ("ticket-sharing", Transport.EntryProducer.of (CedarPooSpec.TicketSharingExample.program, CedarPooSpec.TicketSharingExample.expandedProgram) (fun owner => ((TicketSharingExport.manifest owner)).map Transport.Entry.manifest)),
  ("clinical", Transport.EntryProducer.of CedarPooSpec.ClinicalBreakGlassExample.program (fun owner => ((ClinicalBreakGlassExport.manifest owner)).map Transport.Entry.manifest)),
  ("pseudonymization-validated", Transport.EntryProducer.of CedarPooSpec.PseudonymizationExample.program (fun owner => ((PseudonymizationExport.manifest owner)).map Transport.Entry.manifest)),
  ("pseudonymization-deployable", Transport.EntryProducer.of CedarPooSpec.PseudonymizationExample.program (fun owner => ((PseudonymizationExport.deploymentManifest owner)).map Transport.Entry.artifacts)),
  ("pseudonymization-tabular", Transport.EntryProducer.of PseudonymizationExample.Tabular.fixture (fun outcome => outcome.map Transport.Entry.data)),
  ("agentic-ai-language-model-health-disclosure", Transport.EntryProducer.of CedarPooSpec.AgenticAI.LanguageModel.Disclosure.program (fun owner => ((AgenticAI.LanguageModel.DisclosureExport.manifest owner)).map Transport.Entry.manifest)),
  ("wearable-triage", Transport.EntryProducer.of CedarPooSpec.WearableTriageExample.program (fun owner => ((WearableTriageExport.manifest owner)).map Transport.Entry.manifest)),
  ("model-stewardship", Transport.EntryProducer.of CedarPooSpec.ModelStewardshipExample.program (fun owner => ((ModelStewardshipExample.ReplayExport.manifest owner)).map Transport.Entry.manifest)),
  ("prior-authorization-validated", Transport.EntryProducer.of CedarPooSpec.PriorAuthorizationExample.program (fun owner => ((PriorAuthorizationValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("prior-authorization-malformed", Transport.EntryProducer.of CedarPooSpec.PriorAuthorizationExample.program (fun owner => ((PriorAuthorizationValidatedExport.malformedManifest owner)).map Transport.Entry.manifest)),
  ("prior-authorization-internal-channels", Transport.EntryProducer.of CedarPooSpec.PriorAuthorizationInternalChannels.program (fun owner => ((PriorAuthorizationInternalChannelsExport.manifest owner)).map Transport.Entry.manifest)),
  ("my-health-record-consumer-platform", Transport.EntryProducer.of CedarPooSpec.MyHealthRecordExample.program (fun owner => ((MyHealthRecordExample.ValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("australian-emr-upload", Transport.EntryProducer.of CedarPooSpec.AustralianEMRExample.program (fun owner => ((AustralianEMRExample.ValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("united-states-payer-exchange", Transport.EntryProducer.of CedarPooSpec.UnitedStatesPayerExample.program (fun owner => ((UnitedStatesPayerExample.ValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("attested", Transport.EntryProducer.of CedarPooSpec.AttestedDataAccessExample.program (fun owner => ((AttestedDataAccessExport.manifest owner)).map Transport.Entry.manifest)),
  ("attested-views-validated", Transport.EntryProducer.of CedarPooSpec.AttestedDataAccessExample.program (fun owner => ((AttestedViewsValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("attested-schema-evolution", Transport.EntryProducer.of CedarPooSpec.AttestedDataAccessExample.program (fun owner => (AttestedSchemaEvolutionExport.bundle owner))),
  ("scope-pattern", Transport.EntryProducer.of CedarPooSpec.ScopeAndPatternExample.program (fun owner => ((ScopeAndPatternExport.manifest owner)).map Transport.Entry.manifest)),
  ("scope-pattern-validated", Transport.EntryProducer.of CedarPooSpec.ScopeAndPatternExample.program (fun owner => ((ScopeAndPatternValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("namespaced-enum-validated", Transport.EntryProducer.of CedarPooSpec.NamespacedEnumExample.program (fun owner => ((NamespacedEnumValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("network", Transport.EntryProducer.of CedarPooSpec.TrustedNetworkDataAccessExample.networkProgram (fun owner => ((TrustedNetworkDataAccessExport.manifest owner)).map Transport.Entry.manifest)),
  ("network-validated", Transport.EntryProducer.of CedarPooSpec.TrustedNetworkDataAccessExample.networkProgram (fun owner => ((TrustedNetworkValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("country-approval", Transport.EntryProducer.of CedarPooSpec.CountryApprovalExample.program (fun owner => ((CountryApprovalExport.manifest owner)).map Transport.Entry.manifest)),
  ("country-approval-validated", Transport.EntryProducer.of CedarPooSpec.CountryApprovalExample.program (fun owner => ((CountryApprovalValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("purchase-approval", Transport.EntryProducer.of CedarPooSpec.PurchaseApprovalExample.program (fun owner => ((PurchaseApprovalExport.manifest owner)).map Transport.Entry.manifest)),
  ("delegated-approval", Transport.EntryProducer.of CedarPooSpec.DelegatedApprovalExample.delegatedProgram (fun owner => ((DelegatedApprovalExport.manifest owner)).map Transport.Entry.manifest)),
  ("delegated-matrix", Transport.EntryProducer.of CedarPooSpec.DelegatedApprovalExample.delegatedProgram (fun owner => ((DelegatedApprovalMatrixExport.manifest owner)).map Transport.Entry.manifest)),
  ("payment-release", Transport.EntryProducer.of CedarPooSpec.PaymentReleaseExample.program (fun owner => ((PaymentReleaseExport.manifest owner)).map Transport.Entry.manifest)),
  ("agent-delegation", Transport.EntryProducer.of CedarPooSpec.AgentDelegationExample.program (fun owner => ((AgentDelegationExport.manifest owner)).map Transport.Entry.manifest)),
  ("agent-chain", Transport.EntryProducer.of CedarPooSpec.AgentChainExample.chainProgram (fun owner => ((AgentChainExport.manifest owner)).map Transport.Entry.manifest)),
  ("agent-payment", Transport.EntryProducer.of CedarPooSpec.AgentPaymentExample.paymentProgram (fun owner => ((AgentPaymentExport.manifest owner)).map Transport.Entry.manifest)),
  ("agent-payment-validated", Transport.EntryProducer.of CedarPooSpec.AgentPaymentExample.paymentProgram (fun owner => ((AgentPaymentValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("agent-data-flow", Transport.EntryProducer.of CedarPooSpec.AgentDataFlowExample.program (fun owner => ((AgentDataFlowExport.manifest owner)).map Transport.Entry.manifest)),
  ("agent-data-flow-validated", Transport.EntryProducer.of CedarPooSpec.AgentDataFlowExample.program (fun owner => ((AgentDataFlowValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("lakehouse-gateway-validated", Transport.EntryProducer.of CedarPooSpec.LakehouseGatewayExample.program (fun owner => ((LakehouseGatewayValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("multi-account-banking-validated", Transport.EntryProducer.of CedarPooSpec.MultiAccountBankingExample.program (fun owner => ((MultiAccountBankingValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("reconciliation-validated", Transport.EntryProducer.of CedarPooSpec.AWS.Reconciliation.program (fun owner => ((CedarPooSpec.AWS.Reconciliation.ValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("expense-governance-validated", Transport.EntryProducer.of CedarPooSpec.AWS.Expense.program (fun owner => ((CedarPooSpec.AWS.Expense.ValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("bounded-session", Transport.EntryProducer.of CedarPooSpec.BoundedSessionExample.program (fun owner => ((BoundedSessionExport.manifest owner)).map Transport.Entry.manifest)),
  ("shared-budget", Transport.EntryProducer.of CedarPooSpec.SharedBudgetExample.program (fun owner => ((SharedBudgetExport.manifest owner)).map Transport.Entry.manifest)),
  ("cross-agent-egress-validated", Transport.EntryProducer.of CedarPooSpec.CrossAgentEgressExample.program (fun owner => ((CrossAgentEgressValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("department-synthesis-validated", Transport.EntryProducer.of CedarPooSpec.DepartmentSynthesisExample.program (fun owner => ((DepartmentSynthesisValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("source-custody-validated", Transport.EntryProducer.of CedarPooSpec.SourceCustodyExample.program (fun owner => ((SourceCustodyValidatedExport.manifest owner)).map Transport.Entry.manifest)),
  ("supplier-transition", Transport.EntryProducer.of CedarPooSpec.SupplierTransitionExample.program (fun owner => ((SupplierTransitionExport.manifest owner)).map Transport.Entry.manifest)),
  ("vla-command", Transport.EntryProducer.of CedarPooSpec.VlaCommandBoundaryExample.program (fun owner => ((VlaCommandBoundaryExport.manifest owner)).map Transport.Entry.manifest)),
  ("mission-successor", Transport.EntryProducer.of CedarPooSpec.SuccessorBoundaryExample.program (fun owner => ((SuccessorBoundaryExport.manifest owner)).map Transport.Entry.manifest)),
  ("extension-coverage", Transport.EntryProducer.of CedarPooSpec.ExtensionCoverageExample.program (fun owner => ((ExtensionCoverageExport.manifest owner)).map Transport.Entry.manifest)),
  ("tenant-device", Transport.EntryProducer.of CedarPooSpec.TenantDeviceAuthorizationExample.program (fun owner => ((TenantDevicePolicyEvolutionExport.manifest owner)).map Transport.Entry.manifest))]

def evaluate {α : Type} (produce : Unit → Except String α) : IO α :=
  match produce () with
  | .ok json => pure json
  | .error message => throw (IO.userError message)

/-- Keep compression inside the IO span: pure let bindings may be sunk past clocks. -/
@[noinline] private def serialize (rendering : Thunk (List String)) : IO (List String) :=
  pure rendering.get

/-- Consume complete encoded fragments without allocating another catalog-sized
string. The temporary list prefix can retire as each fragment is written. -/
private def writeChunks (stdout : IO.FS.Stream) : List String → IO Unit
  | [] => stdout.putStr "\n"
  | chunk :: rest => do
      stdout.putStr chunk
      writeChunks stdout rest

@[noinline] private def prepareSources (outputs : List (String × Transport.EntryProducer)) :
    IO (Thunk (List String)) := do
  let encoded ← evaluate (fun _ => Transport.prepareCatalogFrom outputs)
  return encoded.detach

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
      let chunks ← serialize encoded
      phase started "serialized"
      writeChunks (← IO.getStdout) chunks
      phase started "output-written"
  | ["all"] => do
      let outputs ← entries.mapM fun (name, produce) => do
        let json ← evaluate (fun _ => do (← produce.run).toJson)
        pure (name, json)
      for (name, json) in outputs do
        IO.FS.writeFile s!".lake/build/{name}-manifest.json" json.compress
  | [name] =>
      match entries.find? (fun entry => entry.1 == name) with
      | some (_, produce) => do
          let json ← evaluate (fun _ => do (← produce.run).toJson)
          IO.println json.compress
      | none => throw (IO.userError s!"unknown manifest: {name}")
  | _ => throw (IO.userError "expected a manifest name or all")

end CedarPooSpec.Manifests
