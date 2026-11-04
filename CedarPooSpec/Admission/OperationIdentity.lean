import Lean.Data.Json
import LeanPoo.Functional.DeclarativeMetadata

/-!
One authenticated workflow operation remains the same operation across
approval renewal, Agent replanning, and retries. This pure ledger records
admission, not delivery; the Host must persist it transactionally.
-/

namespace CedarPooSpec.Admission
open LeanPoo.Functional.DeclarativeMetadata

structure OperationId where
  value : String
  deriving DecidableEq, BEq, Repr

structure OperationLedger where
  admitted : List OperationId := []
  deriving DecidableEq, BEq, Repr

namespace OperationLedger

def check (ledger : OperationLedger) (id : OperationId) : Bool :=
  !id.value.isEmpty && !ledger.admitted.contains id

def admit (ledger : OperationLedger) (id : OperationId) : Option OperationLedger :=
  if ledger.check id then some { admitted := ledger.admitted ++ [id] } else none

/-- A persisted reservation excludes the same logical operation regardless of
which channel, effect proposal or approval a restarted mediator presents. -/
theorem reserved_operation_refused (ledger next : OperationLedger) (id : OperationId)
    (reserved : ledger.admit id = some next) : next.check id = false := by
  unfold admit at reserved
  split at reserved
  · cases reserved
    have self : (id == id) = true := by
      cases id with
      | mk value =>
        change (value == value) = true
        simp
    simp [check, List.contains_append, self]
  · contradiction

end OperationLedger
structure ReceiverCut where
  scope : String
  generation : Nat
  deriving DecidableEq

/-- The exact effect identity includes the digest of the final observed effect.
Its authenticity and completeness belong to the trusted adapter. -/
structure DispatchBinding where
  operation : OperationId
  effect : String
  cut : ReceiverCut
  deriving DecidableEq

def receiveDispatch (current : ReceiverCut) (request actual : DispatchBinding)
    (ledger : OperationLedger) : Option OperationLedger :=
  if request.cut = current ∧ request = actual then ledger.admit request.operation
  else none

theorem retired_cut_refused (current : ReceiverCut) (request actual : DispatchBinding)
    (ledger : OperationLedger) (retired : request.cut ≠ current) :
    receiveDispatch current request actual ledger = none := by
  simp [receiveDispatch, retired]

theorem receive_requires_exact_current_effect (current : ReceiverCut)
    (request actual : DispatchBinding) (ledger next : OperationLedger)
    (received : receiveDispatch current request actual ledger = some next) :
    request.cut = current ∧ request = actual ∧ next.check request.operation = false := by
  unfold receiveDispatch at received
  split at received
  · rename_i checked
    exact ⟨checked.1, checked.2, OperationLedger.reserved_operation_refused ledger next _ received⟩
  · contradiction

/-- The final recipient invokes this against its actual cut and ledger. -/
def dispatchContract : Contract Unit
    (ReceiverCut × DispatchBinding × DispatchBinding × OperationLedger) OperationLedger where
  input := ⟨"current-receiver-and-observed-effect", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"reserved-logical-operation", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result =>
    receiveDispatch input.1 input.2.1 input.2.2.1 input.2.2.2 = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareDispatch
    (input : ReceiverCut × DispatchBinding × DispatchBinding × OperationLedger) :
    Except String (OperationLedger × Unit) :=
  match receiveDispatch input.1 input.2.1 input.2.2.1 input.2.2.2 with
  | none => .error "stale, mismatched or reserved dispatch"
  | some next => .ok (next, ())

theorem dispatch_invocation_fences_and_reserves
    (receipt : Invocation dispatchContract prepareDispatch (current, request, actual, ledger)) :
    request.cut = current ∧ request = actual ∧ receipt.result.check request.operation = false :=
  receive_requires_exact_current_effect current request actual ledger receipt.result receipt.logic

/-- Authentication is a separate provider-verification premise. Reading a
matching outcome returns its observation and does not edit the send ledger. -/
def reconcileDispatch (reserved observed : DispatchBinding) (authenticated delivered : Bool) :
    Option Bool :=
  if authenticated && decide (reserved = observed) then some delivered else none

theorem reconciliation_requires_independent_exact_binding (reserved observed : DispatchBinding)
    (authenticated delivered : Bool)
    (accepted : reconcileDispatch reserved observed authenticated delivered = some delivered) :
    authenticated = true ∧ reserved = observed := by
  unfold reconcileDispatch at accepted
  split at accepted
  · rename_i checked
    simpa using checked
  · contradiction

end CedarPooSpec.Admission
