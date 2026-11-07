// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
// Source-bound assurance map; the incident's undisclosed exploit mechanics remain unknown.
package FinancialAttackers {
 private import Views::*; private import ScalarValues::*;
 part def Definition; part def KernelLaw; part def HostPremise;
 part capabilityGraph : Definition;
 attribute capabilityGraphSymbol : String = "CedarPooSpec.Attackers.ProfileObject.Model";
 attribute capabilityGraphSource : String = "CedarPooSpec/Attackers/ProfileObject.lean";
 part parentRetention : KernelLaw;
 attribute parentRetentionSymbol : String = "CedarPooSpec.Attackers.ProfileObject.selection_retains_actual_parent";
 attribute parentRetentionSource : String = "CedarPooSpec/Attackers/ProfileObject.lean";
 part capabilityIsolation : KernelLaw;
 attribute capabilityIsolationSymbol : String = "CedarPooSpec.Attackers.ProfileObject.certified_isolation";
 attribute capabilityIsolationSource : String = "CedarPooSpec/Attackers/ProfileObject.lean";
 part traceSafety : KernelLaw;
 attribute traceSafetySymbol : String = "CedarPooSpec.Attackers.run_preserves_outputs";
 attribute traceSafetySource : String = "CedarPooSpec/Attackers/Trace.lean";
 part exactPayment : KernelLaw;
 attribute exactPaymentSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_binds_exact_transaction";
 attribute exactPaymentSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part currentGateway : KernelLaw;
 attribute currentGatewaySymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_retains_gateway";
 attribute currentGatewaySource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part revoked : KernelLaw;
 attribute revokedSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.revoked_cannot_release";
 attribute revokedSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part delegationExposure : KernelLaw;
 attribute delegationExposureSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.pause_preserves_outstanding_authority";
 attribute delegationExposureSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part host : HostPremise;
 attribute hostSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.Current";
 attribute hostSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part scenarioMetadata : Definition;
 attribute scenarioMetadataSymbol : String = "CedarPooSpec.Scenarios.Metadata";
 attribute scenarioMetadataSource : String = "CedarPooSpec/Scenarios/Metadata.lean";
 part scenarioLineage : KernelLaw;
 attribute scenarioLineageSymbol : String = "CedarPooSpec.Scenarios.derivation_retains_parent";
 attribute scenarioLineageSource : String = "CedarPooSpec/Scenarios/Functional.lean";
 part incident : Definition;
 attribute incidentSymbol : String = "CedarPooSpec.Binance2026Scenario.metadata";
 attribute incidentSource : String = "Examples/Scenarios/FinancialServices/Wallet/Binance2026.lean";
 part deploymentPurpose : KernelLaw;
 attribute deploymentPurposeSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.deployment_cannot_release";
 attribute deploymentPurposeSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part transferShape : KernelLaw;
 attribute transferShapeSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_only_native_transfer";
 attribute transferShapeSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part quarantine : KernelLaw;
 attribute quarantineSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentContainment.delegated_cannot_release";
 attribute quarantineSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean";
 part stickyPause : KernelLaw;
 attribute stickyPauseSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentContainment.no_signing_after_pause";
 attribute stickyPauseSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean";
 part retainedBurn : KernelLaw;
 attribute retainedBurnSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentContainment.recovery_retains_burns";
 attribute retainedBurnSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean";
 part clearNoResume : KernelLaw;
 attribute clearNoResumeSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentContainment.observation_cannot_resume";
 attribute clearNoResumeSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean";
 view assurance {
  expose quarantine; expose stickyPause; expose retainedBurn; expose clearNoResume;
  expose deploymentPurpose; expose transferShape;
  expose capabilityGraph; expose parentRetention; expose capabilityIsolation;
  expose traceSafety; expose exactPayment; expose currentGateway;
  expose revoked; expose delegationExposure; expose host;
  expose scenarioMetadata; expose scenarioLineage; expose incident;
  render asInterconnectionDiagram;
 }
}

package WalletSigningProofs {
 private import Views::*; private import ScalarValues::*;
 part def Definition; part def KernelLaw; part def HostPremise;
 part scenario : Definition;
 attribute scenarioSymbol : String = "CedarPooSpec.WalletSigningExample.scenario";
 attribute scenarioSource : String = "Examples/Scenarios/FinancialServices/Wallet/Base.lean";
 part exactPayment : KernelLaw;
 attribute exactPaymentSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_binds_exact_transaction";
 attribute exactPaymentSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part currentGateway : KernelLaw;
 attribute currentGatewaySymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_retains_gateway";
 attribute currentGatewaySource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part revoked : KernelLaw;
 attribute revokedSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.revoked_cannot_release";
 attribute revokedSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part host : HostPremise;
 attribute hostSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.Current";
 attribute hostSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 view assurance {
  expose scenario;
  expose exactPayment;
  expose currentGateway;
  expose revoked;
  expose host;
  render asInterconnectionDiagram;
 }
}

package TenantScenarioProofs {
 private import Views::*; private import ScalarValues::*;
 part def Definition; part def KernelLaw; part def HostPremise;
 part scenario : Definition;
 attribute scenarioSymbol : String = "CedarPooSpec.TenantDeviceAuthorizationExample.scenario";
 attribute scenarioSource : String = "Examples/Scenarios/TenantDevicePolicyEvolution.lean";
 part lineage : KernelLaw;
 attribute lineageSymbol : String = "CedarPooSpec.Scenarios.derivation_retains_parent";
 attribute lineageSource : String = "CedarPooSpec/Scenarios/Functional.lean";
 part provenance : Definition;
 attribute provenanceSymbol : String = "CedarPooSpec.Scenarios.Metadata";
 attribute provenanceSource : String = "CedarPooSpec/Scenarios/Metadata.lean";
 view assurance {
  expose scenario;
  expose lineage;
  expose provenance;
  render asInterconnectionDiagram;
 }
}

// Explanatory required-condition flow; connections are not proof-term uses.
package PaymentDefenseFlow {
 private import Views::*; private import ScalarValues::*;
 part def Definition; part def KernelLaw; part def HostPremise;
 part purpose : KernelLaw;
 attribute purposeSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.deployment_cannot_release";
 attribute purposeSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part approval : KernelLaw;
 attribute approvalSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_requires_current_checks";
 attribute approvalSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part exact : KernelLaw;
 attribute exactSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_binds_exact_transaction";
 attribute exactSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part transferKind : KernelLaw;
 attribute transferKindSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_only_native_transfer";
 attribute transferKindSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part gateway : KernelLaw;
 attribute gatewaySymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_retains_gateway";
 attribute gatewaySource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part host : HostPremise;
 attribute hostSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentContainment.Snapshot";
 attribute hostSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean";
 part joint : Definition;
 attribute jointSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentContainment.release";
 attribute jointSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean";
 part released : KernelLaw;
 attribute releasedSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release_returns_requested_transaction";
 attribute releasedSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean";
 part refused : Definition;
 attribute refusedSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentContainment.release";
 attribute refusedSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean";
 connection flowEdge0 connect purpose to joint;
 connection flowEdge1 connect approval to joint;
 connection flowEdge2 connect exact to joint;
 connection flowEdge3 connect transferKind to joint;
 connection flowEdge4 connect gateway to joint;
 connection flowEdge5 connect host to joint;
 connection flowEdge6 connect joint to released;
 connection flowEdge7 connect joint to refused;
 view defense {
  expose purpose;
  expose approval;
  expose exact;
  expose transferKind;
  expose gateway;
  expose host;
  expose joint;
  expose released;
  expose refused;
  expose flowEdge0;
  expose flowEdge1;
  expose flowEdge2;
  expose flowEdge3;
  expose flowEdge4;
  expose flowEdge5;
  expose flowEdge6;
  expose flowEdge7;
  render asInterconnectionDiagram;
 }
}

// Checked adapter and its independently installed runtime interpretation.
package WalletHostProofs {
 private import Views::*; private import ScalarValues::*;
 part def KernelLaw; part def HostPremise;
 part credential : KernelLaw;
 attribute credentialSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentHost.emission_retains_registrar";
 attribute credentialSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean";
 part facts : KernelLaw;
 attribute factsSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentHost.emission_retains_facts";
 attribute factsSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean";
 part bytes : KernelLaw;
 attribute bytesSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentHost.emission_returns_exact_bytes";
 attribute bytesSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean";
 part durable : KernelLaw;
 attribute durableSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentHost.emission_requires_durable_plan";
 attribute durableSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean";
 part current : KernelLaw;
 attribute currentSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentHost.emission_requires_current_cut";
 attribute currentSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean";
 part once : KernelLaw;
 attribute onceSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentHost.no_second_emission";
 attribute onceSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean";
 part unknown : KernelLaw;
 attribute unknownSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentHost.unknown_cannot_prepare";
 attribute unknownSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean";
 part runtime : HostPremise;
 attribute runtimeSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentHost.Host";
 attribute runtimeSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean";
 view assurance {
  expose credential;
  expose facts;
  expose bytes;
  expose durable;
  expose current;
  expose once;
  expose unknown;
  expose runtime;
  render asInterconnectionDiagram;
 }
}

// Differential replay: source-aware projections, not native incident execution.
package WalletReplayProofs {
 private import Views::*; private import ScalarValues::*;
 part def KernelLaw; part def HostPremise;
 part execution : KernelLaw;
 attribute executionSymbol : String = "CedarPooSpec.Scenarios.Replay.invocation_retains_execution";
 attribute executionSource : String = "CedarPooSpec/Scenarios/Replay.lean";
 part acquisition : KernelLaw;
 attribute acquisitionSymbol : String = "CedarPooSpec.Attackers.ProfileObject.certified_isolation";
 attribute acquisitionSource : String = "CedarPooSpec/Attackers/ProfileObject.lean";
 part writer : KernelLaw;
 attribute writerSymbol : String = "CedarPooSpec.Attackers.ProfileObject.checked_outputs";
 attribute writerSource : String = "CedarPooSpec/Attackers/ProfileObject.lean";
 part settlement : KernelLaw;
 attribute settlementSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentContainment.settlement_retains_exposure";
 attribute settlementSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean";
 part pause : KernelLaw;
 attribute pauseSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentContainment.no_signing_after_pause";
 attribute pauseSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean";
 part runtime : HostPremise;
 attribute runtimeSymbol : String = "CedarPooSpec.Vertical.FinancialServices.PaymentHost.Host";
 attribute runtimeSource : String = "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean";
 view assurance {
  expose execution;
  expose acquisition;
  expose writer;
  expose settlement;
  expose pause;
  expose runtime;
  render asInterconnectionDiagram;
 }
}
