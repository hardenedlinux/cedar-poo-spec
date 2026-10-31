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
  refine ⟨⟨receipt, ⟨7, rfl⟩, ?_, rfl, ?_⟩⟩
  · simp [ZeroTrust.Framework.required, host, security, initial]
  · exact sameState

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

theorem bound_review_cannot_reset_consumption :
    ¬ Nonempty (Final host template prepare 9 {initial with consumed := false}) := by
  rintro ⟨publication⟩
  have retained := final_retains_continuous_authorization publication
  simp [host, security] at retained

#print axioms final_preserves_original_and_binding
#print axioms exact_final_is_admitted
#print axioms replaced_evidence_is_refused
#print axioms cached_matching_review_is_not_current_use
end CedarPooSpec.Gateway.PublicationReviewTest
