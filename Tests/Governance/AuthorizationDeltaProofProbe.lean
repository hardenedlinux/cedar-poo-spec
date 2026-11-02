import CedarPooSpec.Authorization.Delta.OperationalExact
import Examples.Governance.TicketSharing

/-!
Emit the exact SMT-LIB query for the Published -> Posture no-gain case.
This is an audit artifact for external proof-checker experiments. A solver's
UNSAT text or CPC output is not a Lean proof of the query.
-/

namespace CedarPooSpec.AuthorizationDeltaProofProbe

open Cedar.Spec Cedar.Validation Cedar.SymCC
open CedarPooSpec.Authorization.Delta
open CedarPooSpec.TicketSharingExample

def script : IO String := do
  let revision := (model.compileRevision "Published" "Posture").toOption.get
    (by native_decide)
  if schema.environments.length != 1 then
    throw (IO.userError "probe expects exactly one ticket-sharing environment")
  let typeEnv ← match schema.environments.head? with
    | some env => pure env
    | none => throw (IO.userError "ticket-sharing schema has no environment")
  let before ← match wellTypedPolicies revision.beforePolicies typeEnv with
    | .ok policies => pure policies
    | .error error => throw (IO.userError s!"before typecheck: {reprStr error}")
  let after ← match wellTypedPolicies revision.afterPolicies typeEnv with
    | .ok policies => pure policies
    | .error error => throw (IO.userError s!"after typecheck: {reprStr error}")
  let εnv := SymEnv.ofTypeEnv typeEnv
  let asserts ← match verifyErrorFreeAllowExpansion before after εnv with
    | .ok terms => pure terms
    | .error error => throw (IO.userError s!"exact query: {reprStr error}")
  let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
  let solver ← Solver.bufferWriter buffer
  SolverM.run solver do
    let _ ← Encoder.encode asserts εnv (produceModels := false)
    let _ ← Solver.checkSat
    pure ()
  match String.fromUTF8? (← buffer.get).data with
  | some text => pure text
  | none => throw (IO.userError "SMT-LIB encoder produced invalid UTF-8")

end CedarPooSpec.AuthorizationDeltaProofProbe

def main : IO Unit := do
  IO.print (← CedarPooSpec.AuthorizationDeltaProofProbe.script)
