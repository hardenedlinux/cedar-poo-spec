import CedarPooSpec.Authorization.Delta.Reasons
import CedarPooSpec.PolicyJson
import Tests.Governance.AuthorizationDeltaReasonModels

/-!
Two independent grants authorize the same ticket. Removing one changes the
Cedar reason set but not the Allow/Deny decision. A shared incident veto can
mask the reason change, which must remain unresolved rather than certified.
-/

namespace CedarPooSpec.AuthorizationDeltaReasonTest

open Cedar.Spec CedarPooSpec.PolicyModules CedarPooSpec.TicketSharingExample
open CedarPooSpec.Authorization.Delta
open CedarPooSpec.AuthorizationDeltaReasonModels

def run : IO Lean.Json := do
  let .ok changed ← analyzeModelReasons sharedModel "Shared" "OneGrantRemoved" schema
    | throw (IO.userError "reason delta failed")
  if changed.report.decision.impact.classification != "equivalent-in-schema" ||
      changed.report.reasonStable || changed.report.reasonWitnesses.length != 1 ||
      !changed.report.unresolvedPolicyIds.isEmpty then
    throw (IO.userError "same-decision reason change was missed")
  let some edit := changed.report.changes.head?
    | throw (IO.userError "POO edit source missing")
  if changed.report.changes.length != 1 || edit.id != primary.id ||
      edit.beforeOwner.map (·.lastEditedBy) != some "Shared" ||
      edit.afterOwner.isSome ||
      !changed.potentiallyInvalidatedRoots.contains "OneGrantRemoved" then
    throw (IO.userError "reason witness lost C4 edit provenance")
  let some witness := changed.report.reasonWitnesses.head?
    | throw (IO.userError "reason witness missing")
  if witness.beforeResponse.decision != .allow ||
      witness.afterResponse.decision != .allow ||
      !witness.beforeResponse.determiningPolicies.contains primary.id ||
      witness.afterResponse.determiningPolicies.contains primary.id ||
      !witness.afterResponse.determiningPolicies.contains fallback.id then
    throw (IO.userError "invalid reason-change witness")
  let .ok stable ← analyzeModelReasons sharedModel "Shared" "Shared" schema
    | throw (IO.userError "stable reason query failed")
  if !stable.report.reasonStable || stable.report.matchingQueries != 0 then
    throw (IO.userError "unchanged root was not reason-stable")
  let .ok ownerShift ← analyzeModelReasons ownerModel "Shared" "OwnershipShift" schema
    | throw (IO.userError "owner delta query failed")
  let some transfer := ownerShift.report.provenanceChanges.head?
    | throw (IO.userError "same-body owner transfer was missed")
  if ownerShift.report.decision.impact.classification != "equivalent-in-schema" ||
      !ownerShift.report.reasonStable || ownerShift.report.provenanceStable ||
      !ownerShift.report.changes.isEmpty ||
      !ownerShift.report.proof.freshPolicyIds.isEmpty ||
      !ownerShift.report.proof.authorizationDependencies.isEmpty ||
      ownerShift.report.provenanceChanges.length != 1 ||
      transfer.id != primary.id ||
      transfer.beforeOwner.map (·.lastEditedBy) != some "Shared" ||
      transfer.afterOwner.map (·.lastEditedBy) != some "OwnershipShift" ||
      !ownerShift.potentiallyInvalidatedRoots.contains "OwnershipShift" then
    throw (IO.userError "same-body owner transfer was misclassified")
  let .ok masked ← analyzeModelReasons maskedModel "Masked" "MaskedOneRemoved" schema
    | throw (IO.userError "masked reason query failed")
  if masked.report.decision.impact.classification != "equivalent-in-schema" ||
      !masked.report.reasonStable ||
      masked.report.dominatedPolicyIds != [primary.id] ||
      !masked.report.unresolvedPolicyIds.isEmpty ||
      masked.report.dominanceQueries == 0 ||
      !masked.report.reasonWitnesses.isEmpty then
    throw (IO.userError "dominated permit was not certified")
  let .ok beforeCase := CedarPooSpec.PolicyJson.authorizationCase
      "reason-before" "Shared" sharedModel "Shared"
      witness.witness.request witness.witness.entities
    | throw (IO.userError "could not export before reason witness")
  let .ok afterCase := CedarPooSpec.PolicyJson.authorizationCase
      "reason-after" "OneGrantRemoved" sharedModel "OneGrantRemoved"
      witness.witness.request witness.witness.entities
    | throw (IO.userError "could not export after reason witness")
  return Lean.Json.mkObj [
    ("decision_delta", Lean.toJson changed.report.decision.impact.classification),
    ("reason_policy", Lean.toJson witness.policyId),
    ("reason_stable", Lean.toJson changed.report.reasonStable),
    ("before_owner", Lean.toJson (edit.beforeOwner.map (·.lastEditedBy))),
    ("invalidated_roots", Lean.toJson changed.potentiallyInvalidatedRoots),
    ("masked_reason_stable", Lean.toJson masked.report.reasonStable),
    ("masked_dominated", Lean.toJson masked.report.dominatedPolicyIds),
    ("masked_unresolved", Lean.toJson masked.report.unresolvedPolicyIds),
    ("masked_dominance_queries", Lean.toJson masked.report.dominanceQueries),
    ("stable_same_root", Lean.toJson stable.report.reasonStable),
    ("owner_shift_reason_stable", Lean.toJson ownerShift.report.reasonStable),
    ("owner_shift_provenance_stable", Lean.toJson ownerShift.report.provenanceStable),
    ("owner_shift_changed_policy_ids", Lean.toJson (ownerShift.report.changes.map (·.id))),
    ("owner_shift_policy", Lean.toJson transfer.id),
    ("owner_shift_before_owner", Lean.toJson (transfer.beforeOwner.map (·.lastEditedBy))),
    ("owner_shift_after_owner", Lean.toJson (transfer.afterOwner.map (·.lastEditedBy))),
    ("manifest", Lean.Json.mkObj [("cases", Lean.toJson [beforeCase, afterCase])])]

end CedarPooSpec.AuthorizationDeltaReasonTest

def main : IO Unit := do
  IO.println (← CedarPooSpec.AuthorizationDeltaReasonTest.run).compress
