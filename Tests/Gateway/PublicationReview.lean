import CedarPooSpec.Gateway.PublicationReview

namespace CedarPooSpec.Gateway.PublicationReviewTest
open LeanPoo.Functional.DeclarativeMetadata
open PublicationReview

-- Read access remains public, but constructing a mixed analysis/snapshot pair
-- through the public API must be rejected by the elaborator.
#check_failure fun (a _b : Authorization.Delta.ReviewedInteraction) =>
  ({ a with analysis := _b.analysis } : Authorization.Delta.ReviewedInteraction)
#check_failure fun (_a : Authorization.Delta.ReviewedInteraction) =>
  ({ analysis := _a.analysis, snapshot := _a.snapshot } : Authorization.Delta.ReviewedInteraction)

structure View where
  parent : Nat
  artifact : Nat
  cut : Nat
  pending : Bool
  current : Bool
  consumed : Bool
  held : Nat
  deriving DecidableEq

abbrev Result := Nat × (Nat × Option Nat) × Nat
def initial : View := ⟨2, 7, 4, false, true, true, 4⟩
def security : ZeroTrust.Framework Nat View where
  authenticated := fun _ => True
  authorized := fun _ _ => True
  currentAtUse := fun view => view.current = true
  consumptionCommitted := fun _ view => view.consumed = true
  unknownRetained := fun _ view => view.held = 4
  revoked := fun _ _ => False
  mediated := fun _ _ => True

def host : Host Nat Result View Nat Nat Nat where
  security := security
  parentAt := View.parent
  approvedEvidenceAt := fun view _ => some view.artifact
  registrationCommitted := fun _ _ artifact => artifact = 7
  registryRecovered := fun _ => True
  registrarCurrent := fun _ _ => True
  cutAt := View.cut
  projection := id
  pendingAdmissible := fun _ view => view.pending = false
  commit := fun before _ after => after = before

def template : Contract Unit Nat Result where
  input := ⟨"input", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"output", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => inferInstance
  rule := .truth

def result : Result := (9, (2, some 7), 4)
def prepare (view : View) (_ : Nat) : Except Unit (Result × View) := .ok (result, view)

-- Original acceptance remains possible; this adapter is not deny-all.
theorem exact_binding_is_admitted :
    ∃ receipt, (host.contract template 9 initial).invoke (prepare initial) 9 = .ok receipt ∧
      receipt.result = result ∧ receipt.state = initial := by
  apply Contract.invoke_accepts <;>
    simp [Host.contract, Contract.bindEvidence, Formula.Holds, Formula.relabel,
      host, template, prepare, result, initial]

theorem exact_final_is_admitted : Nonempty (Final host template prepare 9 initial) := by
  obtain ⟨receipt, _, _, sameState⟩ := exact_binding_is_admitted
  refine ⟨⟨receipt, ⟨7, rfl⟩, ?_, True.intro, True.intro, ?_, rfl, sameState⟩⟩
  · intro artifact present
    simpa [host, initial] using present.symm
  · simp [ZeroTrust.Framework.required, host, security, initial]

-- Matching reference bindings do not replace the original invocation rule.
def refusing : Contract Unit Nat Result := {template with rule := .deny .truth}
#guard !((host.contract refusing 9 initial).invoke (prepare initial) 9).isOk

-- The old result is internally consistent, but the independent deciding parent
-- or review reference changed. A caller cannot repair this by rebasing labels.
theorem replaced_evidence_is_refused :
    ¬ Nonempty (Final host template prepare 9 {initial with artifact := 8}) := by
  apply changed_binding_cannot_commit
  intro pair called
  cases called
  decide

theorem old_parent_is_refused :
    ¬ Nonempty (Final host template prepare 9 {initial with parent := 3}) := by
  apply changed_binding_cannot_commit
  intro pair called
  cases called
  decide

theorem changed_cut_is_refused :
    ¬ Nonempty (Final host template prepare 9 {initial with cut := 5}) := by
  apply changed_binding_cannot_commit
  intro pair called
  cases called
  decide

-- pending denotes an unresolved external source dependency in this fixture,
-- not this command's own staged administrative intent.
theorem unqualified_pending_blocks_even_with_matching_evidence :
    ¬ Nonempty (Final host template prepare 9 {initial with pending := true}) :=
  unqualified_pending_cannot_commit (by simp [host])

theorem cached_matching_review_is_not_current_use :
    ¬ Nonempty (Final host template prepare 9 {initial with current := false}) :=
  stale_use_cannot_commit (by simp [host, security])

theorem missing_registry_entry_cannot_commit :
    ¬ Nonempty (Final {host with approvedEvidenceAt := fun _ _ => none} template prepare 9 initial) :=
  missing_review_cannot_commit rfl

theorem local_entry_without_anchor_cannot_commit :
    ¬ Nonempty (Final {host with registrationCommitted := fun _ _ _ => False} template prepare 9 initial) :=
  unanchored_registration_cannot_commit (fun _ => id)

theorem matching_rolled_back_registry_cannot_commit :
    ¬ Nonempty (Final {host with registryRecovered := fun _ => False} template prepare 9 initial) :=
  unrecovered_registry_cannot_commit id

theorem matching_old_worker_cannot_commit :
    ¬ Nonempty (Final {host with registrarCurrent := fun _ _ => False} template prepare 9 initial) :=
  old_registrar_cannot_commit id

abbrev Binding := RegistrarBinding Nat Nat Nat Nat Nat
def credential : Binding := ⟨1, 2, 8, 7, 9, 3, 10⟩
def identity : RegistrarAuthority Nat Bool Nat Nat Nat Nat Nat where
  current := fun _ => credential
  issued := fun _ _ => True
  roleAllowed := fun subject _ => subject = 1
  expectedScope := fun _ => 7
  expectedAudience := fun _ => 9
  revoked := fun _ revoked => revoked = true
  possession := fun _ command _ => command = 9

theorem exact_credential_can_authorize_command : identity.admitted credential 9 false := by
  simp [RegistrarAuthority.admitted, identity, credential]

theorem shared_subject_is_not_incarnation :
    identity.roleAllowed credential.subject false ∧
      ¬ identity.admitted {credential with incarnation := 4} 9 false := by
  constructor
  · rfl
  · exact substituted_registrar_binding_is_refused (by decide)

theorem matching_identity_with_wrong_key_is_refused :
    ¬ identity.admitted {credential with publicKey := 11} 9 false :=
  substituted_registrar_binding_is_refused (by decide)

theorem matching_identity_with_wrong_epoch_is_refused :
    ¬ identity.admitted {credential with epoch := 4} 9 false :=
  substituted_registrar_binding_is_refused (by decide)

theorem revoked_exact_identity_is_refused : ¬ identity.admitted credential 9 true :=
  revoked_registrar_binding_is_refused rfl

theorem possession_for_another_command_is_refused : ¬ identity.admitted credential 10 false :=
  unbound_registrar_command_is_refused (by simp [identity])

def registrarForView (command : Nat) (view : View) : Prop :=
  identity.admitted credential command (!view.current)

theorem identity_binding_reaches_final_publication
    (final : Final {host with registrarCurrent := registrarForView} template prepare 9 initial) :
    identity.possession credential 9 (!initial.current) := by
  have bound := registrar_admission_retains_exact_binding final.fenced
  exact bound.2.2

theorem bound_review_cannot_reset_consumption :
    ¬ Nonempty (Final host template prepare 9 {initial with consumed := false}) := by
  rintro ⟨publication⟩
  have retained := final_retains_continuous_authorization publication
  simp [host, security] at retained

#print axioms final_preserves_original_and_binding
#print axioms registrar_admission_retains_exact_binding
#print axioms shared_subject_is_not_incarnation
#print axioms identity_binding_reaches_final_publication
#print axioms exact_final_is_admitted
#print axioms replaced_evidence_is_refused
#print axioms cached_matching_review_is_not_current_use

-- All original reference/currentness checks can match while the referenced
-- analysis is absent. The semantic adapter must still refuse publication.
theorem matching_reference_without_analysis_is_refused
    (modelAt : View → PolicyModules.Model) (schemaAt : View → Cedar.Validation.Schema)
    (stateAt : View → Authorization.Delta.ReleaseState) :
    ¬ Nonempty (Final (host.withDeltaReview (fun _ _ _ => none)
      modelAt schemaAt stateAt (fun _ _ _ _ => true)) template prepare 9 initial) :=
  unresolved_delta_cannot_commit (fun _ => rfl)

#print axioms delta_final_retains_exact_review
#print axioms unresolved_delta_cannot_commit
#print axioms matching_reference_without_analysis_is_refused


private def publishingHost : Host Nat Result View Nat Nat Nat :=
  { host with commit := fun before _ after => after.cut = before.cut + 1 }
private def publish (view : View) (_ : Nat) : Except Unit (Result × View) :=
  .ok (result, {view with cut := view.cut + 1})
private def activeAt (active next : Authorization.Delta.ReleaseState) (view : View) :=
  if view.cut = 4 then active else next

-- Positive integration: use the actual resolved review and its accepted next
-- state in Final, while retaining the original Contract and all use guards.
-- The premise can be obtained from the public analyzer/release transition; it
-- is not a new constructor for an unreviewed analysis/snapshot pair.
theorem accepted_analysis_can_reach_final
    (reviewed : Authorization.Delta.ReviewedInteraction)
    (model : PolicyModules.Model) (schema : Cedar.Validation.Schema)
    (active next : Authorization.Delta.ReleaseState) (policies : Cedar.Spec.Policies)
    (advanced : reviewed.advanceReviewed model schema active (fun _ _ => false) = .ok (next, policies)) :
    Nonempty (Final (publishingHost.withDeltaReview (fun _ _ _ => some reviewed)
      (fun _ => model) (fun _ => schema) (activeAt active next) (fun _ _ _ _ => false))
      template publish 9 initial) := by
  obtain ⟨receipt, _, sameResult, sameState⟩ :=
    Contract.invoke_accepts (contract := publishingHost.contract template 9 initial)
      (execute := publish initial) (args := 9) (result := result)
      (state := {initial with cut := 5}) (by trivial) (by rfl) (by trivial) (by
        simp [Host.contract, Contract.bindEvidence, Formula.Holds, Formula.relabel,
          publishingHost, host, template, result, initial])
  refine ⟨⟨receipt, ⟨7, rfl⟩, ?_, True.intro, True.intro, ?_, rfl, ?_⟩⟩
  · intro artifact present
    simpa [Host.withDeltaReview, publishingHost, host, initial] using present.symm
  · simp [Host.withDeltaReview, publishingHost, ZeroTrust.Framework.required, host, security, initial]
  · constructor
    · simp [publishingHost, sameState, initial]
    · refine ⟨7, reviewed, policies, rfl, rfl, ?_⟩
      simpa [sameResult, sameState, activeAt, initial] using advanced

#print axioms accepted_analysis_can_reach_final
#print axioms rejected_delta_cannot_commit
#print axioms delta_final_retires_resolved_review
#print axioms Authorization.Delta.ReviewedInteraction.advanceReviewed_postcondition
#print axioms Authorization.Delta.ReviewedInteraction.returned_state_rejects_republication

end CedarPooSpec.Gateway.PublicationReviewTest
