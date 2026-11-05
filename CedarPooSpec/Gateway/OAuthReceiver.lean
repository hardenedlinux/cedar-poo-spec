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

structure Handoff where
  previousActive : String
  previousImage : Image
  cut : Admission.ReceiverCut
  deriving DecidableEq

/-- The independent authority retains the complete acknowledged image and
the only active placement. Native code uses a canonical digest for equality. -/
structure Checkpoint where
  active : String
  image : Image
  handoff : Option Handoff := none
  oauthAuthority : Option String := none
  receiverAuthority : String := ""
  deriving DecidableEq

def Checkpoint.binding (checkpoint : Checkpoint) : Revocation.Crash.ReceiverBinding :=
  ⟨checkpoint.receiverAuthority, checkpoint.image.cut.scope⟩

def Checkpoint.permits (checkpoint : Checkpoint) (placement : String) (image : Image) : Prop :=
  checkpoint.active = placement ∧ checkpoint.image = image

structure PromotionInput where
  independent : Option Checkpoint
  expected : Checkpoint
  candidate : Image
  placement : String

def promote (input : PromotionInput) : Option Checkpoint := do
  let pin ← input.independent
  if pin = input.expected ∧ input.placement ≠ "" ∧ input.placement ≠ pin.active ∧
      input.candidate = pin.image then
    let image ← advance input.candidate input.candidate.cut
    return ⟨input.placement, image, some ⟨pin.active, pin.image, image.cut⟩,
      pin.oauthAuthority, pin.receiverAuthority⟩
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
      receipt.result.image.delivered = pin.image.delivered ∧ input.expected = pin ∧
      receipt.result.handoff = some ⟨pin.active, pin.image, receipt.result.image.cut⟩ := by
  have accepted := receipt.logic
  change promote input = some receipt.result at accepted
  cases present : input.independent with
  | none => simp [promote, present] at accepted
  | some pin =>
    simp only [promote, present, bind, Option.bind] at accepted
    split at accepted
    · rename_i checked
      simp [advance] at accepted
      rw [← accepted, checked.2.2.2]
      exact ⟨pin, rfl, rfl, rfl, checked.2.2.1, rfl, rfl, rfl, rfl, checked.1.symm, rfl⟩
    · contradiction

theorem promotion_preserves_oauth_authority
    (receipt : Invocation promotionContract preparePromotion input)
    (present : input.independent = some pin) :
    receipt.result.oauthAuthority = pin.oauthAuthority := by
  have accepted := receipt.logic
  change promote input = some receipt.result at accepted
  simp only [promote, present, bind, Option.bind] at accepted
  split at accepted
  · simp [advance] at accepted
    rw [← accepted]
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
  obtain ⟨actual, source, _, _, _, _, _, _, delivered, _, _⟩ := promotion_retains_acknowledged_delivery receipt
  have same : actual = pin := Option.some.inj (source.symm.trans present)
  simp only [evidence, delivered, same]

theorem consecutive_promotions_keep_signed_evidence
    (first : Invocation promotionContract preparePromotion input)
    (second : Invocation promotionContract preparePromotion next)
    (initial : input.independent = some pin) (successor : next.independent = some first.result)
    (operation : Admission.OperationId) :
    evidence second.result.image operation = evidence pin.image operation :=
  (promotion_keeps_signed_evidence second successor operation).trans
    (promotion_keeps_signed_evidence first initial operation)

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

theorem promotion_checkpoint_changed (present : input.independent = some pin)
    (changed : pin ≠ input.expected) : promote input = none := by
  simp [promote, present, changed]

/-- With one serialized independent checkpoint, a second contender cannot
consume the same predecessor, even if it has the winner's exact image. -/
theorem promotion_cannot_consume_checkpoint_twice
    (winner : Invocation promotionContract preparePromotion input)
    (retry : PromotionInput) (current : retry.independent = some winner.result)
    (expected : retry.expected = input.expected) : promote retry = none := by
  obtain ⟨pin, _, _, _, _, _, advanced, _, _, predecessor, _⟩ :=
    promotion_retains_acknowledged_delivery winner
  apply promotion_checkpoint_changed current
  rw [expected, predecessor]
  intro same
  rw [same] at advanced
  omega

structure PromotionRecovery where
  independent : Option Checkpoint
  expected : Checkpoint
  placement : String
  replica : Image

def recoverPromotion (input : PromotionRecovery) : Option Admission.ReceiverCut := do
  let pin ← input.independent
  let handoff ← pin.handoff
  if pin.active = input.placement ∧ pin.image = input.replica ∧
      handoff.previousActive = input.expected.active ∧ handoff.previousImage = input.expected.image then
    some handoff.cut
  else none

def promotionRecoveryContract : Contract Unit PromotionRecovery Admission.ReceiverCut where
  input := ⟨"active-replica-and-observed-predecessor", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"recorded-handoff-cut", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => recoverPromotion input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def preparePromotionRecovery (input : PromotionRecovery) : Except String (Admission.ReceiverCut × Unit) :=
  match recoverPromotion input with
  | some cut => .ok (cut, ())
  | none => .error "receiver promotion recovery refused"

theorem committed_promotion_ack_can_recover
    (receipt : Invocation promotionContract preparePromotion input) :
    recoverPromotion ⟨some receipt.result, input.expected, input.placement, receipt.result.image⟩ =
      some receipt.result.image.cut := by
  obtain ⟨pin, _, _, placement, _, _, _, _, _, predecessor, handoff⟩ :=
    promotion_retains_acknowledged_delivery receipt
  simp [recoverPromotion, handoff, placement, predecessor]

theorem inactive_placement_cannot_recover_promotion (present : input.independent = some pin)
    (inactive : pin.active ≠ input.placement) : recoverPromotion input = none := by
  cases handoff : pin.handoff <;> simp [recoverPromotion, present, handoff, inactive]

structure ManagedInput where
  independent : Option Checkpoint
  placement : String
  delivery : Input
  authorization : Revocation.Crash.BeginInput

structure ManagedResult where
  oauth : Revocation.Crash.Image
  receiver : Checkpoint
  deriving DecidableEq

/-- A successful observation reserves the exact OAuth intent and checks the
active receiver in one serialized step. The native adapter commits the OAuth
burn first, so an interrupted receiver commit may still leave that burn. -/
def receiveManaged (input : ManagedInput) : Option ManagedResult := do
  let pin ← input.independent
  let oauth ← Revocation.Crash.begin input.authorization
  if pin.active = input.placement ∧ pin.image = input.delivery.image ∧
      pin.oauthAuthority = some input.authorization.image.oauth.checkpoint.authorityId ∧
      input.authorization.intent = input.delivery.witnessed ∧
      pin.receiverAuthority ≠ "" ∧ input.authorization.receiver = some pin.binding then
    let image ← receive input.delivery
    return ⟨oauth, { pin with image }⟩
  else none

def managedContract : Contract Unit ManagedInput ManagedResult where
  input := ⟨"active-receiver-and-current-OAuth-authority", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"OAuth-burn-and-independently-committed-delivery", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => receiveManaged input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareManaged (input : ManagedInput) : Except String (ManagedResult × Unit) :=
  match receiveManaged input with
  | some result => .ok (result, ())
  | none => .error "managed receiver dispatch refused"

/-- Recover the durable OAuth reservation when the receiver checkpoint
never advanced. This branch has no receiver completion witness. -/
def recoverReservation
    (reservation : Invocation Revocation.Crash.beginContract Revocation.Crash.prepareBegin input)
    (before : Checkpoint) : ManagedResult :=
  ⟨reservation.result, before⟩

theorem managed_retains_oauth_reservation
    (receipt : Invocation managedContract prepareManaged input) :
    Revocation.Crash.begin input.authorization = some receipt.result.oauth := by
  have accepted := receipt.logic
  change receiveManaged input = some receipt.result at accepted
  cases present : input.independent with
  | none => simp [receiveManaged, present] at accepted
  | some pin =>
    cases reserved : Revocation.Crash.begin input.authorization with
    | none => simp [receiveManaged, present, reserved] at accepted
    | some oauth =>
      simp only [receiveManaged, present, reserved, bind, Option.bind] at accepted
      split at accepted
      · cases delivered : receive input.delivery with
        | none => simp [delivered] at accepted
        | some image =>
          simp [delivered] at accepted
          rw [← accepted]
      · contradiction

theorem reservation_without_receiver_commit
    (reservation : Invocation Revocation.Crash.beginContract Revocation.Crash.prepareBegin input)
    (before : Checkpoint) :
    let recovered := recoverReservation reservation before
    recovered.receiver = before ∧
      (recovered.oauth.retained.any (fun entry =>
        entry.intent.operation == input.operation)) = true :=
  ⟨rfl, Revocation.Crash.begin_records_burn reservation⟩

theorem fenced_placement_cannot_receive (present : input.independent = some pin)
    (fenced : ¬ pin.permits input.placement input.delivery.image) :
    receiveManaged input = none := by
  change ¬ (pin.active = input.placement ∧ pin.image = input.delivery.image) at fenced
  cases oauth : Revocation.Crash.begin input.authorization <;>
    simp [receiveManaged, present, oauth, ← and_assoc, fenced]

theorem refused_oauth_cannot_receive (input : ManagedInput)
    (refused : Revocation.Crash.begin input.authorization = none) : receiveManaged input = none := by
  cases present : input.independent <;> simp [receiveManaged, present, refused]

theorem reserved_operation_refused_after_failover
    (retry : ManagedInput) (before : Revocation.Crash.Image)
    (burned : (before.retained.any fun entry => entry.intent.operation == retry.authorization.operation) = true)
    (retained : retry.authorization.image.retained = before.retained) :
    receiveManaged retry = none := by
  apply refused_oauth_cannot_receive
  exact Revocation.Crash.burned_operation_cannot_begin _ (retained.symm ▸ burned)

theorem stale_oauth_replica_cannot_receive (input : ManagedInput)
    (stale : input.authorization.read.replica ≠ input.authorization.image.oauth.checkpoint) :
    receiveManaged input = none := by
  apply refused_oauth_cannot_receive
  let final : Revocation.Recovery.FinalInput :=
    ⟨input.authorization.image.oauth.checkpoint.authorityId,
      some input.authorization.image.oauth, input.authorization.read⟩
  have refused := Revocation.Recovery.cannot_finalize_from_failed_recovery final
    (Revocation.Recovery.stale_replica_cannot_recover rfl stale)
  change Revocation.Recovery.finalize
    ⟨input.authorization.image.oauth.checkpoint.authorityId,
      some input.authorization.image.oauth, input.authorization.read⟩ = none at refused
  cases anchor : input.authorization.history.independent <;>
    simp [Revocation.Crash.begin, anchor, refused]

theorem revoked_grant_cannot_receive (input : ManagedInput)
    (linked : input.authorization.image.oauth.checkpoint.ledger.accessEntry
      input.authorization.read.attempt.grant.tokenHash = some entry)
    (revoked : entry.family ∈ input.authorization.image.oauth.checkpoint.ledger.revoked) :
    receiveManaged input = none := by
  apply refused_oauth_cannot_receive
  have refused := Revocation.Recovery.durable_revocation_blocks_final
    (input := ⟨input.authorization.image.oauth.checkpoint.authorityId,
      some input.authorization.image.oauth, input.authorization.read⟩) rfl linked revoked
  cases anchor : input.authorization.history.independent <;>
    simp [Revocation.Crash.begin, anchor, refused]

structure ManagedReconciliation where
  independent : Option Checkpoint
  placement : String
  replica : Image
  audit : Revocation.Crash.ReconcileInput

/-- The current receiver checkpoint supplies the committed outcome. The
incoming audit bundle cannot choose its own receiver or outcome. -/
def reconcileManaged (input : ManagedReconciliation) : Option Revocation.Crash.Image := do
  let pin ← input.independent
  if pin.active = input.placement ∧ pin.image = input.replica ∧
      pin.oauthAuthority = some input.audit.image.oauth.checkpoint.authorityId ∧
      pin.receiverAuthority ≠ "" then
    let (_, outcome) ← evidence pin.image ⟨input.audit.operation⟩
    Revocation.Crash.reconcileFrom input.audit (some ⟨pin.binding, outcome⟩)
  else none

def managedReconciliationContract : Contract Unit ManagedReconciliation Revocation.Crash.Image where
  input := ⟨"independent-receiver-checkpoint-and-provider-audit", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"settlement-bound-to-committed-receiver-outcome", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => reconcileManaged input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareManagedReconciliation (input : ManagedReconciliation) :
    Except String (Revocation.Crash.Image × Unit) :=
  match reconcileManaged input with
  | some result => .ok (result, ())
  | none => .error "managed receiver reconciliation refused"

theorem managed_reconciliation_pins_committed_outcome
    (receipt : Invocation managedReconciliationContract prepareManagedReconciliation input)
    (present : input.independent = some pin)
    (committed : evidence pin.image ⟨input.audit.operation⟩ = some (action, outcome)) :
    receipt.result.settledOutcome outcome.receipt.commit.operation = some outcome := by
  have accepted := receipt.logic
  change reconcileManaged input = some receipt.result at accepted
  simp only [reconcileManaged, present, bind, Option.bind] at accepted
  split at accepted
  · have applied : Revocation.Crash.reconcileFrom input.audit (some ⟨pin.binding, outcome⟩) =
        some receipt.result := by simpa [committed] using accepted
    exact Revocation.Crash.reconciliation_from_pins_committed_outcome applied
  · contradiction

theorem conflict_first_cannot_settle (present : input.independent = some pin)
    (committed : evidence pin.image ⟨input.audit.operation⟩ = some (action, outcome))
    (missing : outcome ∉ input.audit.outcomes) : reconcileManaged input = none := by
  simp [reconcileManaged, present, committed,
    Revocation.Crash.missing_committed_outcome_refuses_recovery input.audit ⟨pin.binding, outcome⟩ missing]

end CedarPooSpec.Gateway.OAuth.Receiver
