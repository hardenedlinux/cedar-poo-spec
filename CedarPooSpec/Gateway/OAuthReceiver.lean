import CedarPooSpec.Gateway.OAuthRevocationCrash
import CedarPooSpec.Admission.OperationIdentity

/-! The receiver atomically installs the current cut, stable operation
reservation and simulated provider observation. Sender authentication and
provider signatures are verified by the native adapter. -/
namespace CedarPooSpec.Gateway.OAuth.Receiver
open Gateway.EffectProtocol LeanPoo.Functional.DeclarativeMetadata

structure Delivery where
  dispatch : Admission.DispatchBinding
  channel : String
  outcome : ProviderOutcome
  deriving DecidableEq

structure Image where
  cut : Admission.ReceiverCut
  operations : Admission.OperationLedger := {}
  delivered : List Delivery := []
  deriving DecidableEq

def advance (image : Image) (expected : Admission.ReceiverCut) : Option Image :=
  if expected = image.cut then
    some { image with cut := { image.cut with generation := image.cut.generation + 1 } }
  else none

theorem advance_preserves_delivery (advanced : advance image expected = some next) :
    next.cut.scope = image.cut.scope ∧ next.cut.generation = image.cut.generation + 1 ∧
    next.operations = image.operations ∧ next.delivered = image.delivered := by
  unfold advance at advanced
  split at advanced
  · rw [← Option.some.inj advanced]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · contradiction

structure Input where
  image : Image
  request : Delivery
  actual : Admission.DispatchBinding
  observedChannel : String
  witnessed : CommitRef
  senderAuthenticated : Bool

/-- Channel is authenticated and checked, while deduplication remains keyed
only by the stable operation selected by the existing admission ledger. -/
def receive (input : Input) : Option Image := do
  if input.senderAuthenticated = true ∧ input.observedChannel ≠ "" ∧
      input.request.channel = input.observedChannel ∧
      input.request.outcome.version.supported = true ∧
      input.request.outcome.domain = "cedar-poo/provider-outcome" ∧
      input.request.outcome.receipt.commit = input.witnessed ∧
      input.witnessed.operation = input.request.dispatch.operation.value ∧
      input.request.outcome.receipt.action.operation = input.witnessed.operation ∧
      (input.image.delivered.filter
        (fun entry => decide (entry.dispatch.operation = input.request.dispatch.operation))) = [] then
    let operations ← Admission.receiveDispatch input.image.cut input.request.dispatch input.actual
      input.image.operations
    return { input.image with operations, delivered := input.request :: input.image.delivered }
  else none

def contract : Contract Unit Input Image where
  input := ⟨"authenticated-dispatch-and-current-receiver", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"atomic-receiver-reservation-and-signed-result", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => receive input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : Input) : Except String (Image × Unit) :=
  match receive input with
  | some image => .ok (image, ())
  | none => .error "provider dispatch refused"

theorem receive_retains_reservation_and_outcome
    (receipt : Invocation contract prepare input) :
    receipt.result.operations.check input.request.dispatch.operation = false ∧
    receipt.result.delivered = input.request :: input.image.delivered ∧
    (input.image.delivered.filter
      (fun entry => decide (entry.dispatch.operation = input.request.dispatch.operation))) = [] := by
  have accepted := receipt.logic
  change receive input = some receipt.result at accepted
  unfold receive at accepted
  split at accepted
  · rename_i valid
    obtain ⟨_, _, _, _, _, _, _, _, fresh⟩ := valid
    cases reserved : Admission.receiveDispatch input.image.cut input.request.dispatch input.actual
        input.image.operations with
    | none => simp [reserved] at accepted
    | some operations =>
      simp [reserved] at accepted
      rw [← accepted]
      exact ⟨(Admission.receive_requires_exact_current_effect _ _ _ _ _ reserved).2.2, rfl, fresh⟩
  · contradiction

theorem old_cut_refused (input : Input) (old : input.request.dispatch.cut ≠ input.image.cut) :
    receive input = none := by
  simp [receive, Admission.retired_cut_refused _ _ _ _ old]

theorem reserved_operation_refused (input : Input)
    (reserved : input.image.operations.check input.request.dispatch.operation = false) :
    receive input = none := by
  simp [receive, Admission.receiveDispatch, Admission.OperationLedger.admit, reserved]

theorem cut_advance_keeps_no_resend
    (receipt : Invocation contract prepare input)
    (advanced : advance receipt.result expected = some reopened) (retry : Input)
    (current : retry.image = reopened)
    (same : retry.request.dispatch.operation = input.request.dispatch.operation) :
    receive retry = none := by
  apply reserved_operation_refused
  rw [current, (advance_preserves_delivery advanced).2.2.1, same]
  exact (receive_retains_reservation_and_outcome receipt).1

theorem committed_cut_refuses_old_dispatch (advanced : advance image expected = some reopened)
    (retry : Input) (current : retry.image = reopened)
    (old : retry.request.dispatch.cut = image.cut) : receive retry = none := by
  apply old_cut_refused
  intro equal
  rw [current, old] at equal
  have generation := congrArg Admission.ReceiverCut.generation equal
  rw [(advance_preserves_delivery advanced).2.1] at generation
  omega

/-- Independent read of a completed operation. It has no execution transition. -/
def evidence (image : Image) (operation : Admission.OperationId) : Option (AuditRecord × ProviderOutcome) :=
  match image.delivered.filter (fun delivery => decide (delivery.dispatch.operation = operation)) with
  | [delivery] => some (delivery.outcome.receipt.action, delivery.outcome)
  | _ => none

theorem committed_receipt_recovered (receipt : Invocation contract prepare input) :
    evidence receipt.result input.request.dispatch.operation =
      some (input.request.outcome.receipt.action, input.request.outcome) := by
  have retained := (receive_retains_reservation_and_outcome receipt).2
  rw [evidence, retained.1]
  simp [retained.2]

end CedarPooSpec.Gateway.OAuth.Receiver
