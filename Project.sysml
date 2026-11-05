// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
// Project entry and source ownership, not runtime authorization or proof closure.
package CedarProject {
 private import ScalarValues::*;
 attribute typescriptRoot : String = "dev/ts";
 attribute sysmlRoot : String = "dev/sysml";
 attribute quintRoot : String = "dev/qnt";
 attribute modelSources : String[1..*] = (
  "dev/sysml/architecture.sysml",
  "dev/sysml/security-frameworks.sysml",
  "dev/sysml/zero-trust-proofs.sysml",
  "dev/sysml/gateway-activities.sysml",
  "dev/sysml/lean-catalog.sysml",
  "dev/sysml/attackers.sysml"
 );
 attribute scenarioFigures : String[1..*] = (
  "Examples/Scenarios/FinancialServices/Wallet/Base.d2",
  "Examples/Scenarios/FinancialServices/Wallet/Binance2026.d2",
  "Examples/Scenarios/FinancialServices/Wallet/Binance2026Assurance.d2",
  "Examples/Scenarios/FinancialServices/Wallet/Binance2026Host.d2",
  "Examples/Scenarios/FinancialServices/Wallet/Binance2026Replay.d2",
  "Examples/Scenarios/TenantDevicePolicyEvolution.d2"
 );
 part def SharedDefinitions; part def ProductionProfile; part def Scenario;
 part def VerificationMethod; part def DevelopmentSource; part def ExternalBoundary;
 part project {
  part definitions : SharedDefinitions;
  part productions : ProductionProfile;
  part payment : Scenario;
  part health : Scenario;
  part attackers : SharedDefinitions;
  part lean : VerificationMethod;
  part quint : VerificationMethod;
  part sysml : VerificationMethod;
  part typescript : DevelopmentSource;
  part host : ExternalBoundary;
 }
 dependency definitionsToProduction from project::productions to project::definitions;
 dependency paymentUsesAttackers from project::payment to project::attackers;
 dependency healthUsesAttackers from project::health to project::attackers;
 dependency attackerDefinitions from project::attackers to project::definitions;
 dependency paymentProof from project::lean to project::payment;
 dependency threatExploration from project::quint to project::attackers;
 dependency parsedViews from project::typescript to project::sysml;
 dependency executionPremises from project::productions to project::host;
}
