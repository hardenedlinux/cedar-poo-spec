import CedarPooSpec.Authorization.Delta.EffectiveReasons
import CedarPooSpec.PolicyJson
import Tests.Governance.AuthorizationDeltaReasonModels

/-!
The effective-reason query distinguishes a hidden policy match from a change
to Cedar's final determining-policy set. It also checks an effect flip and an
owner-only overlay without treating POO provenance as Cedar semantics.
-/

namespace CedarPooSpec.AuthorizationDeltaEffectiveReasonTest

open Cedar.Spec CedarPooSpec.PolicyModules CedarPooSpec.Authorization.Delta
open CedarPooSpec.AuthorizationDeltaReasonModels CedarPooSpec.TicketSharingExample

def effectModel : Model :=
  (sharedModel.extend "EffectFlip" "Shared"
    [.overlay { primary with effect := .forbid }]).toOption.get (by native_decide)

def run : IO Lean.Json := do
  let .ok changed ← analyzeModelEffectiveReasons sharedModel
      "Shared" "OneGrantRemoved" schema
    | throw (IO.userError "effective reason query failed")
  let some witness := changed.report.reasonWitnesses.find? (·.policyId == primary.id)
    | throw (IO.userError "removed grant lacks effective reason witness")
  if changed.report.decision.impact.classification != "equivalent-in-schema" ||
      changed.report.solverReasonStable ||
      !witness.beforeResponse.determiningPolicies.contains primary.id ||
      witness.afterResponse.determiningPolicies.contains primary.id then
    throw (IO.userError "same-decision effective reason change was missed")
  let .ok masked ← analyzeModelEffectiveReasons maskedModel
      "Masked" "MaskedOneRemoved" schema
    | throw (IO.userError "masked effective reason query failed")
  if !masked.report.solverReasonStable ||
      !masked.report.reasonWitnesses.isEmpty || masked.report.policyQueries == 0 then
    throw (IO.userError "veto-masked grant changed final reasons")
  let .ok ownerShift ← analyzeModelEffectiveReasons ownerModel
      "Shared" "OwnershipShift" schema
    | throw (IO.userError "owner-only effective reason query failed")
  if !ownerShift.report.solverReasonStable || ownerShift.report.provenanceStable ||
      ownerShift.report.policyQueries != 0 then
    throw (IO.userError "owner-only overlay was mistaken for Cedar behavior")
  let .ok flipped ← analyzeModelEffectiveReasons effectModel
      "Shared" "EffectFlip" schema
    | throw (IO.userError "effect-flip reason query failed")
  let .ok conservativeFlip ← analyzeModelReasons effectModel
      "Shared" "EffectFlip" schema
    | throw (IO.userError "conservative effect-flip query failed")
  if conservativeFlip.report.reasonStable ||
      conservativeFlip.report.unresolvedPolicyIds != [primary.id] then
    throw (IO.userError "effect flip was incorrectly certified by conservative query")
  let some flipWitness := flipped.report.reasonWitnesses.find? (·.policyId == fallback.id)
    | throw (IO.userError "effect flip lacks effective reason witness")
  if flipped.report.solverReasonStable ||
      flipWitness.beforeResponse.decision != .allow ||
      flipWitness.afterResponse.decision != .deny then
    throw (IO.userError "effect flip was misclassified")
  let .ok revision := sharedModel.compileRevision "Shared" "OneGrantRemoved"
    | throw (IO.userError "could not compile duplicate-ID regression")
  let some repeated := revision.before.policies.head?
    | throw (IO.userError "duplicate-ID regression has no policy")
  let duplicate :=
    { revision with before :=
      { revision.before with policies := revision.before.policies ++ [repeated] } }
  match ← analyzeEffectiveReasons duplicate schema with
  | .error (.duplicatePolicyIds "before") => pure ()
  | _ => throw (IO.userError "duplicate policy ID was admitted by effective reasons")
  match ← analyzeReasons duplicate schema with
  | .error (.duplicatePolicyIds "before") => pure ()
  | _ => throw (IO.userError "duplicate policy ID was admitted by conservative reasons")
  let some repeatedAfter := revision.after.policies.head?
    | throw (IO.userError "after-side duplicate regression has no policy")
  let afterDuplicate :=
    { revision with after :=
      { revision.after with policies := revision.after.policies ++ [repeatedAfter] } }
  match ← analyzeEffectiveReasons afterDuplicate schema with
  | .error (.duplicatePolicyIds "after") => pure ()
  | _ => throw (IO.userError "duplicate after-policy ID was admitted")
  match ← analyzeReasons afterDuplicate schema with
  | .error (.duplicatePolicyIds "after") => pure ()
  | _ => throw (IO.userError "duplicate after-policy ID was admitted by conservative reasons")
  let .ok beforeCase := CedarPooSpec.PolicyJson.authorizationCase
      "effective-reason-before" "Shared" sharedModel "Shared"
      witness.witness.request witness.witness.entities
    | throw (IO.userError "could not export before reason witness")
  let .ok afterCase := CedarPooSpec.PolicyJson.authorizationCase
      "effective-reason-after" "OneGrantRemoved" sharedModel "OneGrantRemoved"
      witness.witness.request witness.witness.entities
    | throw (IO.userError "could not export after reason witness")
  return Lean.Json.mkObj [
    ("changed_decision_delta", Lean.toJson changed.report.decision.impact.classification),
    ("changed_policy", Lean.toJson witness.policyId),
    ("changed_reason_stable", Lean.toJson changed.report.solverReasonStable),
    ("masked_reason_stable", Lean.toJson masked.report.solverReasonStable),
    ("masked_queries", Lean.toJson masked.report.policyQueries),
    ("owner_reason_stable", Lean.toJson ownerShift.report.solverReasonStable),
    ("owner_provenance_stable", Lean.toJson ownerShift.report.provenanceStable),
    ("owner_queries", Lean.toJson ownerShift.report.policyQueries),
    ("flip_reason_stable", Lean.toJson flipped.report.solverReasonStable),
    ("flip_before_decision", Lean.toJson (if flipWitness.beforeResponse.decision == .allow then "allow" else "deny")),
    ("flip_after_decision", Lean.toJson (if flipWitness.afterResponse.decision == .allow then "allow" else "deny")),
    ("duplicate_ids_rejected", Lean.toJson true),
    ("manifest", Lean.Json.mkObj [("cases", Lean.toJson [beforeCase, afterCase])])]

end CedarPooSpec.AuthorizationDeltaEffectiveReasonTest

def main : IO Unit := do
  IO.println (← CedarPooSpec.AuthorizationDeltaEffectiveReasonTest.run).compress
