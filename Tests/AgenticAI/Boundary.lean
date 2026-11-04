import CedarPooSpec.AgenticAI.Boundary
import CedarPooSpec.Data.CumulativeDisclosure

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
