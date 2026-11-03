import Productions.Gateway.EffectProtocol

namespace CedarPooSpec.Gateway.EffectProtocolTest
open Gateway.EffectProtocol CedarPooSpec.ZeroTrust CedarPooSpec.Production.EffectProtocol

#guard faults.length == 32
#guard faults.eraseDups.length == 32
#guard auditCases.length == 13
#guard (auditCases.map (fun row => row.1)).eraseDups.length == 13
#guard ((faults.map (simulate · true)).filter (·.sent)).length == 2
#guard (faults.map (simulate · false)).all (fun outcome => outcome == ⟨false,false,false,false,false⟩)
#guard simulate .logFailure true == ⟨true,false,false,false,false⟩
#guard simulate .crashAfterSend true == ⟨true,true,true,false,true⟩

private def earlier : CommitRef := ⟨"operation", [0], [1]⟩
private def later : CommitRef := ⟨"operation", [2], [3]⟩
private def action : AuditRecord := ⟨"operation", "original"⟩
private def ambiguousReport := reconcile [action] [⟨action, later⟩] 0 true [earlier, later]
#guard ambiguousReport.unresolvedPrecommits == ["operation"]
#guard ambiguousReport.duplicates == ["operation"]
#guard !ambiguousReport.clean
#guard resolves [action] ⟨action, later⟩ later
#guard !resolves [action] ⟨action, later⟩ earlier
#guard !resolves [] ⟨action, later⟩ later

private def original : Requirement Envelope Current := fun envelope current =>
  accepts current envelope true = true
private def profile := CedarPooSpec.ZeroTrust.ProfileObject.define "EvidenceBoundEffect" original
#guard profile.isOk
#guard (profile.toOption.map fun object =>
  (CedarPooSpec.ZeroTrust.ProfileObject.openSession original object).isOk) == some true

theorem selected_contract_retains_original
    {object : CedarPooSpec.ZeroTrust.ProfileObject.Object original}
    (session : CedarPooSpec.ZeroTrust.ProfileObject.Session original object)
    (selected : CedarPooSpec.ZeroTrust.ProfileObject.Profile original)
    (read : session.read .profile = some selected)
    (accepted : selected.requirement envelope current) :
    original envelope current :=
  (CedarPooSpec.ZeroTrust.ProfileObject.selected_child_preserves_original session selected read accepted).2

-- Two different typed records cannot safely share a delimiter encoding.
private def ambiguous (left right : String) : String := left ++ "|" ++ right
example : ("a", "b|c") ≠ ("a|b", "c") := by decide
example : ambiguous "a" "b|c" = ambiguous "a|b" "c" := by decide

#print axioms receipt_bound_effect_is_error_free
#print axioms precommit_without_observation_remains_unresolved
#print axioms another_receipt_cannot_hide_precommit
#print axioms duplicate_precommit_is_reported
#print axioms resolved_commit_is_exact
#print axioms different_commit_cannot_resolve
#print axioms missing_receipt_iff
#print axioms affected_iff
#print axioms missing_action_iff
#print axioms accepted_effect_is_exact
#print axioms accepted_fact_is_current_and_verified
#print axioms claimed_fact_is_refused
#print axioms unverified_fact_is_refused
#print axioms accepted_inventory_covers_required
#print axioms send_requires_precommit
#print axioms unknown_outcome_has_no_receipt
#print axioms selected_contract_retains_original
end CedarPooSpec.Gateway.EffectProtocolTest
