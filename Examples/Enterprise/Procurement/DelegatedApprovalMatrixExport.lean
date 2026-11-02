import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Procurement.DelegatedApproval

/-!
A finite cross-product checks the independent procurement rule and the
Lean-to-Rust Cedar authorization boundary across both final revisions.
-/

namespace CedarPooSpec.DelegatedApprovalMatrixExport

open Cedar.Spec
open CedarPooSpec.DelegatedApprovalExample
open CedarPooSpec.PurchaseApprovalExample

def amounts : List String := ["-1.0000", "0.0000", "250.0000", "500.0000", "500.0001"]

def expectedDecision (root : String) (principal resource agent : EntityUID)
    (requested : String) : Decision :=
  if root == "Delegated" && principal == bob && resource == operationsOrder &&
      agent == purchasingBot && (requested == "250.0000" || requested == "500.0000")
  then .allow else .deny

def cases : List (String × String × Request × Decision) := Id.run do
  let mut rows := []
  for root in ["Delegated", "Revoked"] do
    for principal in [alice, bob] do
      for resource in [operationsOrder, researchOrder] do
        for agent in [purchasingBot, aliceBot, dormantBot, missingBot] do
          for requested in amounts do
            rows := (s!"matrix-{rows.length}", root,
              delegatedRequest principal resource agent requested,
              expectedDecision root principal resource agent requested) :: rows
  return rows.reverse

def exact
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.DelegatedApprovalExample.delegatedModel CedarPooSpec.DelegatedApprovalExample.delegatedSchema :=
      CedarPooSpec.DelegatedApprovalExample.delegatedProgram) : Bool := cases.all fun (_, root, req, expected) =>
  match owner.response root req delegatedEntities with
  | .error _ => false
  | .ok response =>
      response.decision == expected && response.erroringPolicies.isEmpty

theorem exactFully : exact = true := by native_decide

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.DelegatedApprovalExample.delegatedModel CedarPooSpec.DelegatedApprovalExample.delegatedSchema :=
      CedarPooSpec.DelegatedApprovalExample.delegatedProgram) : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← cases.mapM fun (name, root, req, _) =>
    owner.case name root.toLower root req delegatedEntities
  return { cases := exported }

end CedarPooSpec.DelegatedApprovalMatrixExport
