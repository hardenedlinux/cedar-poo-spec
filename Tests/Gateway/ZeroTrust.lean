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
#print axioms ZeroTrust.continuing_objects_preserve_parent_and_consumption

-- The current state is projected into the actual Cedar context. Keeping the
-- initial permit, profile and source does not keep Allow when this fact changes.
private def currentState (view : View) : Bool := view.floor == 0
private def currentPrepared (view : View) : Gateway.Prepared String Bool request :=
  { prepared with operation := ⟨"invoke", currentState view⟩ }
private def activeRelease : Authorization.Delta.ReleaseState :=
  ⟨"base", [permitPolicy], .enforcing, context.policyRevision⟩
private def currentAssessment := ZeroTrust.currentAdmission profile host currentPrepared
  (fun _ => model) currentState (fun _ => checks) (fun _ => entities) (fun _ => activeRelease)

theorem current_receipt_constructs_assessment
    (receipt : Gateway.Receipt (currentPrepared initial) model "invoke" (currentState initial)
      initial.context checks entities) : currentAssessment "invoke" initial := by
  refine ⟨receipt, by decide, ?_⟩
  apply (Authorization.Delta.ReleaseState.matchesCurrent_iff _ _ _).mpr
  refine ⟨rfl, ?_, rfl, rfl⟩
  have compiled : (model.compile "base").toOption = some [permitPolicy] := by native_decide
  have current := congrArg Except.toOption receipt.cedar.compiled
  change (model.compile "base").toOption = some receipt.cedar.policies at current
  rw [compiled] at current
  exact Option.some.inj current

#guard (Gateway.authorize (currentPrepared initial) model "invoke" (currentState initial)
  initial.context checks entities).isOk
#guard !(Gateway.authorize (currentPrepared {initial with floor := 1}) model "invoke" false
  initial.context checks entities).isOk

-- An initial receipt has the wrong state index for the fresh current world.
#check_failure fun (receipt : Gateway.Receipt (currentPrepared initial) model "invoke" true
    initial.context checks entities) =>
  (show Gateway.Receipt (currentPrepared {initial with floor := 1}) model "invoke" false
    initial.context checks entities from receipt)

theorem denied_current_world_has_no_assessment :
    ¬ currentAssessment "invoke" {initial with floor := 1} := by
  rintro ⟨receipt, _⟩
  have accepted := Gateway.admitted_actual_request_is_error_free receipt
  have compiled : (model.compile "base").toOption = some [permitPolicy] := by native_decide
  have current := congrArg Except.toOption receipt.cedar.compiled
  change (model.compile "base").toOption = some receipt.cedar.policies at current
  rw [compiled] at current
  have same := Option.some.inj current
  rw [← same] at accepted
  have denied : let response := Cedar.Spec.isAuthorized (request "invoke" false) entities [permitPolicy]
    (response.decision == .allow && response.erroringPolicies.isEmpty) = false := by native_decide
  change (let response := Cedar.Spec.isAuthorized (request "invoke" false) entities [permitPolicy]
    (response.decision == .allow && response.erroringPolicies.isEmpty)) = true at accepted
  rw [denied] at accepted
  contradiction

-- A model can still compile an old root while the independent active release
-- has changed. A valid Cedar receipt alone therefore cannot establish current use.
private def assessRelease (release : Authorization.Delta.ReleaseState) :=
  ZeroTrust.authorizeCurrent profile host currentPrepared (fun _ => model)
    currentState (fun _ => checks) (fun _ => entities) (fun _ => release) "invoke" initial

#guard (assessRelease activeRelease).isOk
#guard !(assessRelease {activeRelease with activeRoot := "restricted"}).isOk
#guard !(assessRelease {activeRelease with activePolicies := [denyPolicy]}).isOk
#guard !(assessRelease {activeRelease with executionMode := .observing}).isOk
#guard !(assessRelease {activeRelease with executionMode := .disabled}).isOk
#guard !(assessRelease {activeRelease with epoch := 2}).isOk

-- This witness exposes the old gap without adding a compatibility API: a valid
-- receipt/refinement can coexist with a different active root in the same view.
theorem receipt_without_release_binding_is_insufficient
    (receipt : Gateway.Receipt (currentPrepared initial) model "invoke" (currentState initial)
      initial.context checks entities) :
    (∃ _sameReceipt : Gateway.Receipt (currentPrepared initial) model "invoke" (currentState initial)
      initial.context checks entities, profile.Refines (currentPrepared initial).profile) ∧
    ({activeRelease with activeRoot := "restricted"} : Authorization.Delta.ReleaseState).activeRoot ≠
      (currentPrepared initial).policy.root :=
  ⟨⟨receipt, by decide⟩, by decide⟩

theorem observing_release_has_no_current_admission :
    ¬ ZeroTrust.currentAdmission profile host currentPrepared (fun _ => model)
      currentState (fun _ => checks) (fun _ => entities)
      (fun _ => {activeRelease with executionMode := .observing}) "invoke" initial := by
  rintro ⟨_, _, matched⟩
  have enforced := (Authorization.Delta.ReleaseState.matchesCurrent_iff _ _ _).mp matched
  cases enforced.2.2.1

theorem changed_active_root_has_no_current_admission :
    ¬ ZeroTrust.currentAdmission profile host currentPrepared (fun _ => model)
      currentState (fun _ => checks) (fun _ => entities)
      (fun _ => {activeRelease with activeRoot := "restricted"}) "invoke" initial := by
  rintro ⟨_, _, matched⟩
  have root := ((Authorization.Delta.ReleaseState.matchesCurrent_iff _ _ _).mp matched).1
  contradiction

#print axioms Authorization.Delta.ReleaseState.matchesCurrent_iff
#print axioms ZeroTrust.current_admission_binds_active_release
#print axioms receipt_without_release_binding_is_insufficient
#print axioms observing_release_has_no_current_admission
#print axioms changed_active_root_has_no_current_admission
#print axioms ZeroTrust.current_admission_has_error_free_allow
#print axioms ZeroTrust.continuing_current_admission_preserves_delta
#print axioms denied_current_world_has_no_assessment

end CedarPooSpec.Gateway.ZeroTrustTest
