import CedarPooSpec.Gateway.ZeroTrust
import Tests.Gateway.Fixture

namespace CedarPooSpec.Gateway.ZeroTrustTest
open GatewayTest

-- Complete Host view has a floor coordinate beyond the public Context. Keeping
-- Context equal is insufficient if the application's deciding image changes.
structure View where
  context : Gateway.Context
  operations : Admission.OperationLedger
  authorities : Admission.AuthorityLedger String
  floor : Nat
  held : Nat

def initial : View := ⟨context, {}, grants, 0, 4⟩
-- Deterministic fixture predicates exercise conditional API composition only;
-- they do not establish authentication, durable commit or native mediation.
def host : ZeroTrust.Host String View where
  context := View.context
  operations := View.operations
  authorities := View.authorities
  authenticated := fun image => image.context.scope = scope
  currentAtUse := fun image => image.floor = 0
  authoritativeProfile := fun original selected published image =>
    original = profile ∧ selected = profile ∧ published = image.context
  committed := fun image after =>
    image.floor = 0 ∧ after.operations.admitted = [⟨scope.canonicalOperation⟩]
  unknownRetained := fun image _ => image.held = 4
  revoked := fun _ => False
  mediated := fun effect image => effect = "invoke" ∧ image.floor = 0

def firstUse : Option Bool := currentPublication.bind fun entry =>
  (Gateway.authorizePublished entry.2 prepared model "invoke" true context checks entities).toOption.bind fun receipt =>
    (ZeroTrust.propose host entry.2 receipt initial rfl "approval").toOption.map fun proposal =>
      (proposal.after.authorities.grants.map (·.used) == [1]) &&
      !(Gateway.consumeAdmission entry.2 receipt proposal.after.operations (grants "new-authority") "new-authority").isOk

#guard firstUse == some true
#guard !(againstCurrent (assessments := [⟨"source", .unknown⟩, ⟨"budget", .satisfied⟩, ⟨"history", .satisfied⟩]))

-- Reuse the actual factory-indexed LeanPoo publication. A raw semantic receipt
-- cannot be passed to the core Zero Trust consumption API.
#check_failure fun (entry : (object : Gateway.ProfileObject.Object) ×
    Gateway.ProfileObject.Publication profile object)
    (raw : Gateway.Receipt prepared model "invoke" true context checks entities) =>
  ZeroTrust.propose host entry.2 raw initial rfl "approval"

section Counterexamples
variable {object : Gateway.ProfileObject.Object}
  {publication : Gateway.ProfileObject.Publication profile object}
  (proposal : ZeroTrust.Proposal host publication prepared model "invoke" true context checks entities)

-- A new floor with identical public context is not the captured complete view.
theorem changed_floor_cannot_finalize
    (old : proposal.before = initial) :
    ¬ ∃ use : ZeroTrust.FinalUse proposal, use.actual = {initial with floor := 1} := by
  apply ZeroTrust.changed_complete_view_cannot_finalize proposal
  intro equality
  have floors := congrArg View.floor equality
  simp [old, initial] at floors

theorem unknown_commit_cannot_finalize :
    ¬ ∃ use : ZeroTrust.FinalUse proposal, use.actual = {initial with floor := 1} := by
  apply ZeroTrust.unknown_or_uncommitted_cannot_finalize proposal
  simp [host, initial]

theorem lost_unknown_hold_cannot_finalize :
    ¬ ∃ use : ZeroTrust.FinalUse proposal, use.actual = {initial with held := 0} := by
  rintro ⟨use, equality⟩
  have retained := use.unknownRetained
  simpa [host, equality] using retained

theorem rolled_back_input_has_no_consumption_prefix (actual : View)
    (empty : (host.operations actual).admitted = []) :
    ¬ Nonempty (ZeroTrust.CommittedPrefix proposal actual) := by
  rintro ⟨evidence⟩
  have installed := congrArg List.length evidence.installed
  have originalPrefix := Gateway.consumption_preserves_operation_prefix publication proposal.receipt
    (host.operations proposal.before) (host.authorities proposal.before) proposal.authorityId
    proposal.after proposal.consumption
  simp [empty, originalPrefix] at installed

end Counterexamples

#print axioms ZeroTrust.zero_trust_final_use
#print axioms ZeroTrust.final_use_has_error_free_cedar_allow
#print axioms ZeroTrust.returned_ledger_rejects_new_authority
#print axioms ZeroTrust.final_use_preserves_authorization_delta
#print axioms changed_floor_cannot_finalize
#print axioms unknown_commit_cannot_finalize
#print axioms lost_unknown_hold_cannot_finalize
#print axioms rolled_back_input_has_no_consumption_prefix
#print axioms ZeroTrust.final_use_satisfies_framework
#print axioms ZeroTrust.framework_object_preserves_gateway_contract
#print axioms ZeroTrust.specialization_preserves_core_and_original
#print axioms ZeroTrust.continuing_use_preserves_original_consumption
end CedarPooSpec.Gateway.ZeroTrustTest
