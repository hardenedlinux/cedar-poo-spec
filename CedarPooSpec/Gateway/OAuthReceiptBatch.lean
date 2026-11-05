import CedarPooSpec.Gateway.OAuthReceiptRecovery

/-! A batch report is transient. Its durable progress is the per-operation
mapping image; a new writer resubmits against that image instead of a cursor. -/
namespace CedarPooSpec.Gateway.OAuth.ReceiptBatch
open LeanPoo.Functional.DeclarativeMetadata

structure State where
  image : ReceiptRecovery.Image
  confirmed : List String := []
  pending : List String := []
  stopped : Option String := none
  deriving DecidableEq

def current (state : State) (item : ReceiptRecovery.Input) : ReceiptRecovery.Input :=
  { item with image := state.image, mode := .settled }

def State.step (state : State) (item : ReceiptRecovery.Input) : State :=
  if state.stopped.isSome then state
  else if item.writer ≠ state.image.oauth.writer ∨ item.recovery.currentReplica = false then
    { state with stopped := some item.request.operation }
  else
    match ReceiptRecovery.contract.invoke ReceiptRecovery.prepare (current state item) with
    | .error _ => { state with pending := item.request.operation :: state.pending }
    | .ok receipt => { state with image := receipt.result, confirmed := item.request.operation :: state.confirmed }

structure Input where
  image : ReceiptRecovery.Image
  items : List ReceiptRecovery.Input

def Input.run (input : Input) : State :=
  let after := input.items.foldl State.step { image := input.image }
  { after with confirmed := after.confirmed.reverse, pending := after.pending.reverse }

def contract : Contract Unit Input State where
  input := ⟨"current-actor-per-item-and-durable-progress", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"confirmed-prefix-pending-evidence-and-fenced-suffix", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => input.run = result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : Input) : Except String (State × Unit) := .ok (input.run, ())

theorem stopped_keeps_prefix (stopped : state.stopped.isSome = true) :
    State.step state item = state := by simp [State.step, stopped]

theorem old_writer_stops (running : state.stopped = none)
    (old : item.writer ≠ state.image.oauth.writer) :
    State.step state item = { state with stopped := some item.request.operation } := by
  simp [State.step, running, old]

theorem old_replica_stops (running : state.stopped = none)
    (old : item.recovery.currentReplica = false) :
    State.step state item = { state with stopped := some item.request.operation } := by
  simp [State.step, running, old]

theorem step_trace (state : State) (item : ReceiptRecovery.Input) :
    ReceiptRecovery.Trace state.image (State.step state item).image := by
  unfold State.step
  split
  · exact .start _
  · split
    · exact .start _
    · split
      · exact .start _
      · rename_i receipt accepted
        exact .commit (.start _) receipt rfl .durable

theorem step_keeps_authorization (state : State) (item : ReceiptRecovery.Input) :
    (State.step state item).image.oauth.oauth = state.image.oauth.oauth := by
  unfold State.step
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i receipt accepted
        exact ReceiptRecovery.persistence_keeps_authorization receipt

theorem accepted_step_binds
    (running : state.stopped = none) (writer : item.writer = state.image.oauth.writer)
    (replica : item.recovery.currentReplica = true)
    (accepted : ReceiptRecovery.contract.invoke ReceiptRecovery.prepare (current state item) = .ok receipt) :
    ReceiptRecovery.lookup (State.step state item).image.rows item.request.identity.operation =
      some (ReceiptRecovery.Request.stored item.request) := by
  simp only [State.step, running, Option.isSome_none, Bool.false_eq_true, ite_false,
    writer, ne_eq, not_true_eq_false, replica, Bool.true_eq_false, or_self]
  simp only [accepted]
  exact ReceiptRecovery.persistence_records receipt

theorem suffix_keeps_committed (items : List ReceiptRecovery.Input)
    (bound : ReceiptRecovery.lookup state.image.rows operation = some row) :
    ReceiptRecovery.lookup (items.foldl State.step state).image.rows operation = some row := by
  induction items generalizing state with
  | nil => exact bound
  | cons item tail ih =>
    apply ih
    exact ReceiptRecovery.trace_preserves_original (step_trace state item) bound

theorem fold_trace (items : List ReceiptRecovery.Input) (state : State) :
    ReceiptRecovery.Trace state.image (items.foldl State.step state).image := by
  induction items generalizing state with
  | nil => exact .start _
  | cons item tail ih =>
    exact ReceiptRecovery.Trace.trans (step_trace state item) (ih (State.step state item))

theorem batch_keeps_original (receipt : Invocation contract prepare input)
    (bound : ReceiptRecovery.lookup input.image.rows operation = some row) :
    ReceiptRecovery.lookup receipt.result.image.rows operation = some row := by
  have same := receipt.logic
  change input.run = receipt.result at same
  rw [← same]
  exact ReceiptRecovery.trace_preserves_original
    (fold_trace input.items { image := input.image }) bound

theorem batch_cannot_resend (receipt : Invocation contract prepare input)
    (retry : Revocation.Crash.BeginInput)
    (burned : (input.image.oauth.retained.any fun entry => entry.intent.operation == retry.operation) = true) :
    Revocation.Crash.begin { retry with image := receipt.result.image.oauth } = none := by
  have same := receipt.logic
  change input.run = receipt.result at same
  rw [← same]
  exact ReceiptRecovery.trace_cannot_resend
    (fold_trace input.items { image := input.image }) retry burned

theorem refused_keeps_image
    (refused : ReceiptRecovery.persist (current state item) = none) :
    (State.step state item).image = state.image := by
  unfold State.step
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i receipt accepted
        have present := receipt.logic.1
        change ReceiptRecovery.persist (current state item) = some receipt.result at present
        simp [refused] at present

theorem fenced_suffix_keeps_prefix (items : List ReceiptRecovery.Input)
    (stopped : state.stopped.isSome = true) : items.foldl State.step state = state := by
  induction items with
  | nil => rfl
  | cons item tail ih => simpa [List.foldl_cons, stopped_keeps_prefix stopped] using ih

theorem append_resumes_same_fold (first second : List ReceiptRecovery.Input) (state : State) :
    (first ++ second).foldl State.step state =
      second.foldl State.step (first.foldl State.step state) := List.foldl_append

/-- Only the durable image survives a worker crash; batch reports and cursors do not. -/
structure RecoveryInput where
  image : ReceiptRecovery.Image
  item : ReceiptRecovery.Input
  boundary : Revocation.Crash.CommitBoundary

def RecoveryInput.run (input : RecoveryInput) : ReceiptRecovery.Image :=
  Revocation.Crash.recoverImage input.boundary input.image
    (State.step { image := input.image } input.item).image

def recoveryContract : Contract Unit RecoveryInput ReceiptRecovery.Image where
  input := ⟨"current-item-and-observed-commit-boundary", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"recovered-image-without-transient-batch-report", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => input.run = result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareRecovery (input : RecoveryInput) : Except String (ReceiptRecovery.Image × Unit) :=
  .ok (input.run, ())

theorem recovery_trace (receipt : Invocation recoveryContract prepareRecovery input) :
    ReceiptRecovery.Trace input.image receipt.result := by
  have same := receipt.logic
  change input.run = receipt.result at same
  rw [← same]
  unfold RecoveryInput.run
  cases input.boundary with
  | staged => exact .start _
  | durable =>
      simpa [Revocation.Crash.recoverImage] using
        step_trace { image := input.image } input.item

theorem recovery_staged_is_before (receipt : Invocation recoveryContract prepareRecovery input)
    (staged : input.boundary = .staged) : receipt.result = input.image := by
  have same := receipt.logic
  change input.run = receipt.result at same
  rw [← same]
  simp [RecoveryInput.run, staged, Revocation.Crash.recoverImage]

theorem recovery_keeps_authorization (receipt : Invocation recoveryContract prepareRecovery input) :
    receipt.result.oauth.oauth = input.image.oauth.oauth := by
  have same := receipt.logic
  change input.run = receipt.result at same
  rw [← same]
  unfold RecoveryInput.run
  cases input.boundary with
  | staged => rfl
  | durable =>
      simpa [Revocation.Crash.recoverImage] using
        step_keeps_authorization { image := input.image } input.item

theorem recovery_keeps_original (receipt : Invocation recoveryContract prepareRecovery input)
    (bound : ReceiptRecovery.lookup input.image.rows operation = some row) :
    ReceiptRecovery.lookup receipt.result.rows operation = some row :=
  ReceiptRecovery.trace_preserves_original (recovery_trace receipt) bound

theorem recovery_refused_is_before (receipt : Invocation recoveryContract prepareRecovery input)
    (refused : ReceiptRecovery.persist (current { image := input.image } input.item) = none) :
    receipt.result = input.image := by
  have same := receipt.logic
  change input.run = receipt.result at same
  rw [← same]
  unfold RecoveryInput.run
  rw [refused_keeps_image refused]
  cases input.boundary <;> rfl

theorem recovery_fenced_is_before (receipt : Invocation recoveryContract prepareRecovery input)
    (old : input.item.writer ≠ input.image.oauth.writer ∨ input.item.recovery.currentReplica = false) :
    receipt.result = input.image := by
  have same := receipt.logic
  change input.run = receipt.result at same
  rw [← same]
  unfold RecoveryInput.run
  have fenced : (State.step { image := input.image } input.item).image = input.image := by
    simp [State.step, old]
  rw [fenced]
  cases input.boundary <;> rfl

theorem recovery_durable_binds (receipt : Invocation recoveryContract prepareRecovery input)
    (durable : input.boundary = .durable)
    (writer : input.item.writer = input.image.oauth.writer)
    (replica : input.item.recovery.currentReplica = true)
    (accepted : ReceiptRecovery.contract.invoke ReceiptRecovery.prepare
      (current { image := input.image } input.item) = .ok mapping) :
    ReceiptRecovery.lookup receipt.result.rows input.item.request.identity.operation =
      some (ReceiptRecovery.Request.stored input.item.request) := by
  have same := receipt.logic
  change input.run = receipt.result at same
  rw [← same]
  simp only [RecoveryInput.run, durable, Revocation.Crash.recoverImage]
  exact accepted_step_binds rfl writer replica accepted

end CedarPooSpec.Gateway.OAuth.ReceiptBatch
