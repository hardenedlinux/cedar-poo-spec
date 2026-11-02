import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Authorization.Delta.Trace
import CedarPooSpec.PolicyJson
import Examples.Enterprise.Agent.Session.BoundedSession

/-!
One proposed agent action sequence is replayed from the same initial session
under two C4 roots. A denied action leaves its side's Host ledger unchanged,
so later requests may have different context even for the same proposal.
-/

namespace CedarPooSpec.BoundedSessionTraceDelta

open CedarPooSpec.Authorization.Delta
open CedarPooSpec.BoundedSessionExample

private def observe (state : Session) (attempt : Attempt) : Cedar.Spec.Env :=
  ⟨request state attempt, entities⟩

private def compare (attempts : List Attempt) :
    Except Error (TraceImpact Session) :=
  compareTrace schema model "Base" "Integrated" ({} : Session)
    attempts observe advance

private def receiptCases
     (name : String) (impact : TraceImpact Session)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.BoundedSessionExample.model CedarPooSpec.BoundedSessionExample.schema :=
      CedarPooSpec.BoundedSessionExample.program) :
    Except String (List Lean.Json) := do
  let indexed := impact.steps.zipIdx
  let before ← indexed.mapM fun (step, index) =>
    programContext.authorizationCase
        s!"{name}-before-{index}" "Base" "Base" step.beforeEnv.request step.beforeEnv.entities
  let after ← indexed.mapM fun (step, index) =>
    programContext.authorizationCase
        s!"{name}-after-{index}" "Integrated" "Integrated" step.afterEnv.request step.afterEnv.entities
  return before ++ after

private def crossReceiptCases
     (name : String) (impact : TraceImpact Session)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.BoundedSessionExample.model CedarPooSpec.BoundedSessionExample.schema :=
      CedarPooSpec.BoundedSessionExample.program) :
    Except String (List Lean.Json) := do
  let indexed := impact.steps.zipIdx
  let beforeOnAfter ← indexed.mapM fun (step, index) =>
    programContext.authorizationCase
        s!"{name}-before-on-after-{index}" "Base" "Base" step.afterEnv.request step.afterEnv.entities
  let afterOnBefore ← indexed.mapM fun (step, index) =>
    programContext.authorizationCase
        s!"{name}-after-on-before-{index}" "Integrated" "Integrated" step.beforeEnv.request step.beforeEnv.entities
  return beforeOnAfter ++ afterOnBefore

def run
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.BoundedSessionExample.model CedarPooSpec.BoundedSessionExample.schema :=
      CedarPooSpec.BoundedSessionExample.program) : IO Lean.Json := do
  let .ok sensitive := compare [readSecret, sendExternal]
    | throw (IO.userError "sensitive-read trace comparison failed")
  if sensitive.steps.map TraceStep.beforeAllowed != [true, true] ||
      sensitive.steps.map TraceStep.afterAllowed != [true, false] ||
      sensitive.steps.map TraceStep.sameInput != [true, true] ||
      sensitive.steps.map TraceStep.directDifference != [false, true] ||
      sensitive.steps.any TraceStep.divergentInputDifference ||
      !sensitive.lost || sensitive.gained ||
      !sensitive.beforeFinal.sensitiveSeen ||
      !sensitive.afterFinal.sensitiveSeen ||
      sensitive.beforeFinal.usedExports != 1 ||
      sensitive.afterFinal.usedExports != 0 ||
      !(sensitive.changes.map (·.id)).contains historyVeto.id then
    throw (IO.userError "sensitive-read trace lost its C4/history delta")
  let .ok budget := compare [readPublic, sendExternal, sendExternal, sendExternal]
    | throw (IO.userError "budget trace comparison failed")
  if budget.steps.map TraceStep.beforeAllowed != [true, true, true, true] ||
      budget.steps.map TraceStep.afterAllowed != [true, true, false, false] ||
      budget.steps.map TraceStep.sameInput != [true, true, true, false] ||
      budget.steps.map TraceStep.directDifference != [false, false, true, false] ||
      budget.steps.map TraceStep.divergentInputDifference != [false, false, false, true] ||
      budget.beforeFinal.usedExports != 3 ||
      budget.afterFinal.usedExports != 1 ||
      !(budget.changes.map (·.id)).contains budgetVeto.id then
    throw (IO.userError "budget trace did not preserve separate Host states")
  let some last := budget.steps.getLast?
    | throw (IO.userError "budget trace has no final proposal")
  if last.beforeEnv.request.context == last.afterEnv.request.context ||
      !last.policyDifferenceAtBeforeInput ||
      !last.policyDifferenceAtAfterInput ||
      last.inputDifferenceUnderBeforePolicy ||
      last.inputDifferenceUnderAfterPolicy then
    throw (IO.userError "budget cross-check changed the observed policy effect")
  let .ok masked := compare [sendExternal "off-task", sendExternal]
    | throw (IO.userError "masked-policy trace comparison failed")
  let some maskedLast := masked.steps.getLast?
    | throw (IO.userError "masked-policy trace has no final proposal")
  if masked.steps.map TraceStep.beforeAllowed != [true, true] ||
      masked.steps.map TraceStep.afterAllowed != [false, true] ||
      maskedLast.sameInput || maskedLast.gained || maskedLast.lost ||
      !maskedLast.policyDifferenceAtBeforeInput ||
      maskedLast.policyDifferenceAtAfterInput ||
      maskedLast.inputDifferenceUnderBeforePolicy ||
      !maskedLast.inputDifferenceUnderAfterPolicy then
    throw (IO.userError "Host ledger did not mask the later policy difference")
  let changedProposal := compareTrace schema model "Base" "Integrated"
      ({} : Session) [readPublic, sendExternal, sendExternal, sendExternal]
      (fun state attempt =>
        observe state (if state.usedExports > 1 then sendInternal else attempt))
      advance
  match changedProposal with
  | .error .operationChanged => pure ()
  | _ => throw (IO.userError "state-dependent operation substitution was admitted")
  let alphabet := [readSecret, sendExternal, sendExternal "off-task"]
  let .ok bounded := compareBoundedTraces schema model "Base" "Integrated"
      ({} : Session) alphabet 3 39 observe advance
    | throw (IO.userError "bounded proposal comparison failed")
  let boundedGains := bounded.filter fun (_, impact) => impact.gained
  let boundedDirectLosses := bounded.filter fun (_, impact) =>
    impact.steps.any fun step => step.directDifference && step.lost
  let boundedDivergentLosses := bounded.filter fun (_, impact) =>
    impact.steps.any fun step => step.divergentInputDifference && step.lost
  let boundedByLength := [1, 2, 3].map fun length =>
    (bounded.filter fun (proposals, _) => proposals.length == length).length
  let boundedInputEffectUnderBefore := bounded.filter fun (_, impact) =>
    impact.steps.any TraceStep.inputDifferenceUnderBeforePolicy
  let boundedInputEffectUnderAfter := bounded.filter fun (_, impact) =>
    impact.steps.any TraceStep.inputDifferenceUnderAfterPolicy
  if bounded.length != 39 || boundedByLength != [3, 9, 27] ||
      !boundedGains.isEmpty ||
      boundedDirectLosses.isEmpty || boundedDivergentLosses.isEmpty then
    throw (IO.userError "bounded scope lost a direct or divergent loss")
  match compareBoundedTraces schema model "Base" "Integrated"
      ({} : Session) alphabet 3 38 observe advance with
  | .error .invalidBoundedScope => pure ()
  | _ => throw (IO.userError "undersized bounded-scope cap was admitted")
  let .ok sensitiveCases := (receiptCases (programContext := programContext)) "sensitive" sensitive
    | throw (IO.userError "cannot export sensitive Cedar replay")
  let .ok budgetCases := (receiptCases (programContext := programContext)) "budget" budget
    | throw (IO.userError "cannot export budget Cedar replay")
  let .ok maskedCases := (receiptCases (programContext := programContext)) "masked" masked
    | throw (IO.userError "cannot export masked Cedar replay")
  let .ok boundedCaseLists := bounded.zipIdx.mapM fun ((_, impact), index) =>
      (receiptCases (programContext := programContext)) s!"bounded-{index}" impact
    | throw (IO.userError "cannot export bounded Cedar replay")
  let boundedCases := boundedCaseLists.flatten
  let .ok sensitiveCrossCases := (crossReceiptCases (programContext := programContext)) "sensitive" sensitive
    | throw (IO.userError "cannot export sensitive cross replay")
  let .ok budgetCrossCases := (crossReceiptCases (programContext := programContext)) "budget" budget
    | throw (IO.userError "cannot export budget cross replay")
  let .ok maskedCrossCases := (crossReceiptCases (programContext := programContext)) "masked" masked
    | throw (IO.userError "cannot export masked cross replay")
  let .ok boundedCrossCaseLists := bounded.zipIdx.mapM fun ((_, impact), index) =>
      (crossReceiptCases (programContext := programContext)) s!"bounded-{index}" impact
    | throw (IO.userError "cannot export bounded cross replay")
  let boundedCrossCases := boundedCrossCaseLists.flatten
  return Lean.Json.mkObj [
    ("sensitive_before", Lean.toJson (sensitive.steps.map TraceStep.beforeAllowed)),
    ("sensitive_after", Lean.toJson (sensitive.steps.map TraceStep.afterAllowed)),
    ("budget_before", Lean.toJson (budget.steps.map TraceStep.beforeAllowed)),
    ("budget_after", Lean.toJson (budget.steps.map TraceStep.afterAllowed)),
    ("masked_before", Lean.toJson (masked.steps.map TraceStep.beforeAllowed)),
    ("masked_after", Lean.toJson (masked.steps.map TraceStep.afterAllowed)),
    ("sensitive_same_input", Lean.toJson (sensitive.steps.map TraceStep.sameInput)),
    ("sensitive_direct_difference", Lean.toJson
      (sensitive.steps.map TraceStep.directDifference)),
    ("budget_same_input", Lean.toJson (budget.steps.map TraceStep.sameInput)),
    ("budget_direct_difference", Lean.toJson
      (budget.steps.map TraceStep.directDifference)),
    ("budget_divergent_input_difference", Lean.toJson
      (budget.steps.map TraceStep.divergentInputDifference)),
    ("sensitive_owner", Lean.toJson
      ((sensitive.changes.find? (·.id == historyVeto.id)).bind
        (fun change => change.afterOwner.map (·.lastEditedBy)))),
    ("different_later_context", Lean.toJson true),
    ("operation_substitution_rejected", Lean.toJson true),
    ("bounded_alphabet_size", Lean.toJson alphabet.length),
    ("bounded_horizon", Lean.toJson (3 : Nat)),
    ("bounded_sequence_count", Lean.toJson bounded.length),
    ("bounded_by_length", Lean.toJson boundedByLength),
    ("bounded_gains", Lean.toJson boundedGains.length),
    ("bounded_direct_loss_sequences", Lean.toJson boundedDirectLosses.length),
    ("bounded_divergent_loss_sequences", Lean.toJson boundedDivergentLosses.length),
    ("bounded_input_effect_under_before_sequences",
      Lean.toJson boundedInputEffectUnderBefore.length),
    ("bounded_input_effect_under_after_sequences",
      Lean.toJson boundedInputEffectUnderAfter.length),
    ("budget_final_policy_diff_at_both_inputs", Lean.toJson true),
    ("budget_final_no_input_decision_diff", Lean.toJson true),
    ("masked_final_policy_diff_at_before_input", Lean.toJson true),
    ("masked_final_input_effect_under_after_policy", Lean.toJson true),
    ("bounded_cap_rejected", Lean.toJson true),
    ("manifest", Lean.Json.mkObj [
      ("cases", Lean.toJson (sensitiveCases ++ budgetCases ++ maskedCases ++
        boundedCases ++ sensitiveCrossCases ++ budgetCrossCases ++
        maskedCrossCases ++ boundedCrossCases))])]

end CedarPooSpec.BoundedSessionTraceDelta

def main : IO Unit := do
  IO.println (← CedarPooSpec.BoundedSessionTraceDelta.run).compress
