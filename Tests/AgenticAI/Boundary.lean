import CedarPooSpec.AgenticAI.Boundary
import CedarPooSpec.Data.CumulativeDisclosure
import CedarPooSpec.Admission.OperationIdentity

namespace Tests.AgenticAI.Boundary

open CedarPooSpec.AgenticAI

def delta : SelectionDelta :=
  { before := ["p1", "p2", "p3"], after := ["p1", "p2"] }

def candidates : List String := ["p1", "p2"]

def reordered : SelectionDelta :=
  { before := ["p1", "p2"], after := ["p2", "p1"] }

def selection : BoundaryFacts :=
  { action := .selectionMutation, sink := .sharedWorkspace,
    intendedSelection := some delta, observedSelection := some delta,
    candidateIds := candidates, outputBound := true, audienceAllowed := true }

theorem selectionRequiresObservedSurvivors :
    admitted selection = true ∧
    admitted { selection with observedSelection := none } = false ∧
    admitted { selection with candidateIds := ["p1"] } = false ∧
    admitted { { selection with intendedSelection := some reordered } with
      observedSelection := some reordered } = false ∧
    admitted { selection with action := .contentWrite } = false := by
  native_decide

theorem sinkAndBaseChecksCannotBeOverridden :
    admitted { selection with audienceAllowed := false } = false ∧
    admitted { selection with outputBound := false } = false ∧
    admitted { selection with sink := .remoteModel } = false ∧
    admitted { { selection with sink := .remoteModel } with
      remoteModelApproved := true } = true := by
  native_decide

/-- A workspace edit and a second-channel tool response can each preserve two
candidates in isolation while their shared history singles out one. -/
theorem isolatedChannelsAdmitButSharedHistoryRefuses :
    let initial : CedarPooSpec.Data.CumulativeDisclosure.Ledger := ⟨["p1", "p2", "p3"], 2⟩
    let workspace := ["p1", "p2"]
    let tool := ["p2", "p3"]
    initial.admits workspace = true ∧ initial.admits tool = true ∧
      (initial.record workspace).bind (fun next => next.record tool) = none ∧
      (initial.record tool).bind (fun next => next.record workspace) = none := by
  decide

end Tests.AgenticAI.Boundary


#print axioms CedarPooSpec.Admission.OperationLedger.reserved_operation_refused
#print axioms CedarPooSpec.Admission.retired_cut_refused
#print axioms CedarPooSpec.Admission.receive_requires_exact_current_effect
#print axioms CedarPooSpec.Admission.reconciliation_requires_independent_exact_binding
#print axioms CedarPooSpec.Admission.dispatch_invocation_fences_and_reserves
#print axioms CedarPooSpec.Admission.sender_commit_retains_all_components
#print axioms CedarPooSpec.Admission.restored_receiver_refuses_old_cut
#print axioms CedarPooSpec.Admission.conflicting_settlement_refused
#print axioms CedarPooSpec.Admission.settlement_invocation_preserves_sender
#print axioms CedarPooSpec.Admission.matching_settlement_idempotent


#print axioms CedarPooSpec.Admission.provider_receipt_preserves_reservation
#print axioms CedarPooSpec.Admission.acknowledged_fence_survives_remote_reopen

open CedarPooSpec.Admission in
theorem staleReplicaCanAcceptPreviouslyUnseenOperation :
    let old : ReceiverCut := ⟨"sink", 7⟩
    let current : ReceiverCut := ⟨"sink", 8⟩
    let request : DispatchBinding := ⟨⟨"new-operation"⟩, "exact-effect", old⟩
    (receiveDispatch old request request {}).isSome = true ∧
      receiveDispatch current request request {} = none := by
  decide
