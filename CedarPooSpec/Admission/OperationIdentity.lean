import CedarPooSpec.Admission.AuthorityConsumption
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

/-- All components restored from one committed sender image. -/
structure SenderImage where
  revision : Nat
  budget : Nat
  approvals : AuthorityLedger String
  operations : OperationLedger
  audit : List DispatchBinding
  deriving DecidableEq

structure SenderCommit where
  expectedRevision : Nat
  approval : String
  dispatch : DispatchBinding
  currentAuthorized : Bool

/-- Current Cedar and cohort checks are supplied by the Host. The resulting
image is persisted as one unit before the adapter can attempt delivery. -/
def SenderImage.commit (state : SenderImage) (request : SenderCommit) : Option SenderImage :=
  if request.expectedRevision = state.revision ∧ state.budget > 0 ∧ request.currentAuthorized then
    match state.approvals.consume request.approval request.dispatch.effect,
        state.operations.admit request.dispatch.operation with
    | .ok approvals, some operations =>
      some ⟨state.revision + 1, state.budget - 1, approvals, operations,
        state.audit ++ [request.dispatch]⟩
    | _, _ => none
  else none

def senderCommitContract : Contract Unit (SenderImage × SenderCommit) SenderImage where
  input := ⟨"current-sender-image", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"atomic-sender-successor", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => input.1.commit input.2 = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareSenderCommit (input : SenderImage × SenderCommit) :
    Except String (SenderImage × Unit) :=
  match input.1.commit input.2 with
  | none => .error "disclosure commit refused"
  | some next => .ok (next, ())

theorem sender_commit_retains_all_components
    (receipt : Invocation senderCommitContract prepareSenderCommit (state, request)) :
    receipt.result.revision = state.revision + 1 ∧
    receipt.result.budget = state.budget - 1 ∧
    state.approvals.consume request.approval request.dispatch.effect = .ok receipt.result.approvals ∧
    receipt.result.operations.check request.dispatch.operation = false ∧
    receipt.result.audit = state.audit ++ [request.dispatch] := by
  have committed := receipt.logic
  change state.commit request = some receipt.result at committed
  unfold SenderImage.commit at committed
  split at committed
  · cases used : state.approvals.consume request.approval request.dispatch.effect <;>
      cases reserved : state.operations.admit request.dispatch.operation <;>
      simp [used, reserved] at committed
    rw [← committed]
    exact ⟨rfl, rfl, rfl, OperationLedger.reserved_operation_refused _ _ _ reserved, rfl⟩
  · contradiction

/-- The old generation cannot match a receiver that reopens its committed cut. -/
theorem restored_receiver_refuses_old_cut
    (request actual : DispatchBinding) (ledger : OperationLedger) (persisted : ReceiverCut)
    (older : request.cut.generation < persisted.generation) :
    receiveDispatch persisted request actual ledger = none := by
  apply retired_cut_refused
  intro equal
  rw [equal] at older
  exact Nat.lt_irrefl _ older

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

/-- A terminal observation can be installed once. Repeated evidence for that
observation is idempotent. A contradictory signed result cannot replace it. -/
def settleDispatch (retained : Option Bool) (reserved observed : DispatchBinding)
    (authenticated delivered : Bool) : Option Bool := do
  let accepted ← reconcileDispatch reserved observed authenticated delivered
  if retained.all (· == accepted) then some accepted else none

theorem conflicting_settlement_refused (reserved observed : DispatchBinding)
    (authenticated retained delivered : Bool) (conflict : retained ≠ delivered) :
    settleDispatch (some retained) reserved observed authenticated delivered = none := by
  simp [settleDispatch, reconcileDispatch, conflict]

theorem matching_settlement_idempotent (binding : DispatchBinding) (delivered : Bool) :
    settleDispatch (some delivered) binding binding true delivered = some delivered := by
  simp [settleDispatch, reconcileDispatch]

structure SettlementInput where
  sender : SenderImage
  retained : Option Bool
  reserved : DispatchBinding
  observed : DispatchBinding
  authenticated : Bool
  delivered : Bool

def prepareSettlement (input : SettlementInput) : Except String (Bool × SenderImage) :=
  match settleDispatch input.retained input.reserved input.observed input.authenticated input.delivered with
  | none => .error "unverified or conflicting outcome"
  | some accepted => .ok (accepted, input.sender)

def settlementContract : Contract Unit SettlementInput Bool where
  input := ⟨"retained-dispatch-and-provider-observation", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"stable-terminal-observation", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result =>
    settleDispatch input.retained input.reserved input.observed input.authenticated input.delivered =
      some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

theorem settlement_invocation_preserves_sender
    (receipt : Invocation settlementContract prepareSettlement input) :
    receipt.state = input.sender := by
  have called := receipt.called
  unfold prepareSettlement at called
  split at called
  · contradiction
  · exact (congrArg Prod.snd (Except.ok.inj called)).symm

end CedarPooSpec.Admission
