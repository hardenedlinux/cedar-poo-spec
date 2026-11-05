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

/-- The independent authority retains the complete acknowledged image and
the only active placement. Native code uses a canonical digest for equality. -/
structure Checkpoint where
  active : String
  image : Image
  deriving DecidableEq

def Checkpoint.permits (checkpoint : Checkpoint) (placement : String) (image : Image) : Prop :=
  checkpoint.active = placement ∧ checkpoint.image = image

structure PromotionInput where
  independent : Option Checkpoint
  candidate : Image
  placement : String

def promote (input : PromotionInput) : Option Checkpoint := do
  let pin ← input.independent
  if input.placement ≠ "" ∧ input.placement ≠ pin.active ∧ input.candidate = pin.image then
    let image ← advance input.candidate input.candidate.cut
    return ⟨input.placement, image⟩
  else none

def promotionContract : Contract Unit PromotionInput Checkpoint where
  input := ⟨"independently-acknowledged-receiver-image-and-candidate", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"promoted-receiver-placement-and-advanced-cut", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => promote input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def preparePromotion (input : PromotionInput) : Except String (Checkpoint × Unit) :=
  match promote input with
  | some checkpoint => .ok (checkpoint, ())
  | none => .error "receiver promotion refused"

theorem different_image_cannot_promote (present : input.independent = some pin)
    (different : input.candidate ≠ pin.image) : promote input = none := by
  simp [promote, present, different]

theorem promotion_retains_acknowledged_delivery
    (receipt : Invocation promotionContract preparePromotion input) :
    ∃ pin, input.independent = some pin ∧ input.candidate = pin.image ∧
      receipt.result.active = input.placement ∧ receipt.result.active ≠ pin.active ∧
      receipt.result.image.cut.scope = pin.image.cut.scope ∧
      receipt.result.image.cut.generation = pin.image.cut.generation + 1 ∧
      receipt.result.image.operations = pin.image.operations ∧
      receipt.result.image.delivered = pin.image.delivered := by
  have accepted := receipt.logic
  change promote input = some receipt.result at accepted
  cases present : input.independent with
  | none => simp [promote, present] at accepted
  | some pin =>
    simp only [promote, present, bind, Option.bind] at accepted
    split at accepted
    · rename_i checked
      simp [advance] at accepted
      rw [← accepted, checked.2.2]
      exact ⟨pin, rfl, rfl, rfl, checked.2.1, rfl, rfl, rfl, rfl⟩
    · contradiction

theorem promotion_fences_previous_placement
    (receipt : Invocation promotionContract preparePromotion input)
    (present : input.independent = some pin) :
    ¬ receipt.result.permits pin.active image := by
  obtain ⟨actual, source, _, _, changed, _⟩ := promotion_retains_acknowledged_delivery receipt
  have same : actual = pin := Option.some.inj (source.symm.trans present)
  exact fun accepted => changed (accepted.1.trans (congrArg Checkpoint.active same).symm)

theorem promotion_keeps_signed_evidence
    (receipt : Invocation promotionContract preparePromotion input)
    (present : input.independent = some pin) (operation : Admission.OperationId) :
    evidence receipt.result.image operation = evidence pin.image operation := by
  obtain ⟨actual, source, _, _, _, _, _, _, delivered⟩ := promotion_retains_acknowledged_delivery receipt
  have same : actual = pin := Option.some.inj (source.symm.trans present)
  simp only [evidence, delivered, same]

theorem promoted_receiver_refuses_same_operation
    (receipt : Invocation promotionContract preparePromotion input)
    (present : input.independent = some pin) (retry : Input)
    (current : retry.image = receipt.result.image)
    (reserved : pin.image.operations.check retry.request.dispatch.operation = false) :
    receive retry = none := by
  obtain ⟨actual, source, _, _, _, _, _, operations, _⟩ := promotion_retains_acknowledged_delivery receipt
  have same : actual = pin := Option.some.inj (source.symm.trans present)
  apply reserved_operation_refused
  rw [current, operations, same]
  exact reserved

structure ManagedInput where
  independent : Option Checkpoint
  placement : String
  delivery : Input

def receiveManaged (input : ManagedInput) : Option Checkpoint := do
  let pin ← input.independent
  if pin.active = input.placement ∧ pin.image = input.delivery.image then
    let image ← receive input.delivery
    return { pin with image }
  else none

def managedContract : Contract Unit ManagedInput Checkpoint where
  input := ⟨"active-receiver-and-exact-independent-image", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"independently-committed-delivery", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => receiveManaged input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareManaged (input : ManagedInput) : Except String (Checkpoint × Unit) :=
  match receiveManaged input with
  | some checkpoint => .ok (checkpoint, ())
  | none => .error "managed receiver dispatch refused"

theorem fenced_placement_cannot_receive (present : input.independent = some pin)
    (fenced : ¬ pin.permits input.placement input.delivery.image) :
    receiveManaged input = none := by
  change ¬ (pin.active = input.placement ∧ pin.image = input.delivery.image) at fenced
  simp only [receiveManaged, present, bind, Option.bind, if_neg fenced]

end CedarPooSpec.Gateway.OAuth.Receiver
