// SPDX-FileCopyrightText: 2026 hardenedlinux Linux Team and Contributors
// SPDX-License-Identifier: Apache-2.0
// Logical specification handoffs, not runtime calls or proof of import conformance.
package CedarFrameworks {
 private import Views::*;
 part def Framework;
 part core : Framework;
 part authorization : Framework;
 part poo : Framework;
 part gateway : Framework;
 part other : Framework;
 connection functionalRequirements connect core to poo;
 connection typedSpecialization connect poo to other;
 connection inheritedProfile connect poo to gateway;
 connection policyAssessment connect authorization to gateway;
 view overview {
  expose core; expose authorization; expose poo; expose gateway; expose other;
  expose functionalRequirements; expose typedSpecialization;
  expose inheritedProfile; expose policyAssessment;
  render asInterconnectionDiagram;
 }
}
