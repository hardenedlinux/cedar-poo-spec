import CedarPooSpec.Gateway.OAuthRevocationRecovery
import CedarPooSpec.Gateway.Lifecycle

/-! Crash recovery keeps writer fencing, the OAuth proof reservation and the
exact effect intent in one authority-owned image. The provider supplies
independent completion evidence. Recovery never authorizes a new send. -/
namespace CedarPooSpec.Gateway.OAuth.Revocation.Crash
open Gateway.EffectProtocol LeanPoo.Functional.DeclarativeMetadata

structure ReceiverBinding where
  checkpoint : String
  scope : String
  deriving DecidableEq

structure ReceiverObservation where
  binding : ReceiverBinding
  outcome : ProviderOutcome

structure Retained where
  intent : CommitRef
  anchor : Gateway.Lifecycle.WitnessFrontier
  providerKey : String
  receiver : Option ReceiverBinding := none
  legacy : Bool := false
  deriving DecidableEq

structure Image where
  oauth : Recovery.Store
  writer : Nat := 0
  retained : List Retained := []
  resolved : List ProviderOutcome := []
  deriving DecidableEq

inductive EffectStatus where
  | unreserved
  | unresolved
  | reconciled
  deriving DecidableEq

def effectStatus (image : Image) (operation : String) : EffectStatus :=
  if image.retained.any (fun entry => entry.intent.operation == operation) then
    if image.resolved.any (fun entry => entry.receipt.commit.operation == operation) then .reconciled
    else .unresolved
  else .unreserved

structure StatusInput where
  image : Image
  writer : Nat
  operation : String

def statusContract : Contract Unit StatusInput EffectStatus where
  input := ⟨"current-OAuth-writer", fun input => input.writer = input.image.writer, fun _ => inferInstance⟩
  output := ⟨"durable-operation-status", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => effectStatus input.image input.operation = result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareStatus (input : StatusInput) : Except String (EffectStatus × Unit) :=
  if input.writer = input.image.writer then .ok (effectStatus input.image input.operation, ())
  else .error "OAuth writer fenced"

/-- A status observation carries the current writer equality; decoding a record
cannot manufacture this premise for an older worker. -/
theorem status_receipt_uses_current_writer
    (receipt : Invocation statusContract prepareStatus input) :
    input.writer = input.image.writer := receipt.input

inductive CommitBoundary where
  | staged
  | durable

/-- A staged write cannot be recovered as a committed image. The durable
image survives even if the acknowledgment was lost. -/
def recoverImage (boundary : CommitBoundary) (before after : α) : α :=
  match boundary with
  | .staged => before
  | .durable => after

def handoff (image : Image) (writer : Nat) : Option Image :=
  if writer = image.writer then some { image with writer := writer + 1 } else none

def revoke (image : Image) (writer : Nat)
    (verified : PAR.VerifiedClient Refresh.RefreshDigest) : Option Image :=
  if writer = image.writer then
    (image.oauth.revoke verified).map (fun next => { image with oauth := next })
  else none

/-- Once contenders use the current writer, either serialization of
revocation and handoff preserves the same durable result. -/
theorem revoke_and_handoff_agree (image : Image) (verified : PAR.VerifiedClient Refresh.RefreshDigest) :
    (revoke image image.writer verified).bind (fun next => handoff next image.writer) =
      (handoff image image.writer).bind (fun next => revoke next (image.writer + 1) verified) := by
  cases applied : image.oauth.revoke verified <;> simp [revoke, handoff, applied]

theorem staged_revoke_preserves_prior (before after : Image) :
    (recoverImage .staged before after).oauth = before.oauth := rfl

theorem durable_revoke_retains_marker
    (applied : revoke before writer verified = some after) :
    (Refresh.RevocationInput.key ⟨before.oauth.checkpoint.ledger, verified⟩) ∈
      (recoverImage .durable before after).oauth.checkpoint.ledger.revoked := by
  unfold revoke at applied
  split at applied
  · cases result : before.oauth.revoke verified with
    | none => simp [result] at applied
    | some next =>
      have equal : { before with oauth := next } = after := by simpa [result] using applied
      rw [← equal]
      exact Recovery.persisted_revocation_marks_family result
  · contradiction

theorem handoff_preserves_effect_state (advanced : handoff before writer = some after) :
    after.retained = before.retained ∧ after.resolved = before.resolved := by
  unfold handoff at advanced
  split at advanced
  · rw [← Option.some.inj advanced]
    exact ⟨rfl, rfl⟩
  · contradiction

theorem revocation_preserves_effect_state (applied : revoke before writer verified = some after) :
    after.retained = before.retained ∧ after.resolved = before.resolved := by
  unfold revoke at applied
  split at applied
  · cases next : before.oauth.revoke verified with
    | none => simp [next] at applied
    | some oauth =>
      have same : { before with oauth } = after := by simpa [next] using applied
      rw [← same]
      exact ⟨rfl, rfl⟩
  · contradiction

theorem effect_status_retained (retained : after.retained = before.retained)
    (resolved : after.resolved = before.resolved) :
    effectStatus after operation = effectStatus before operation := by
  simp [effectStatus, retained, resolved]

theorem effect_status_survives_failover
    (first : handoff before oldWriter = some standby)
    (second : handoff standby standbyWriter = some active)
    (revoked : revoke active activeWriter verified = some after) :
    effectStatus after operation = effectStatus before operation := by
  have h₁ := handoff_preserves_effect_state first
  have h₂ := handoff_preserves_effect_state second
  have h₃ := revocation_preserves_effect_state revoked
  exact (effect_status_retained h₃.1 h₃.2).trans
    ((effect_status_retained h₂.1 h₂.2).trans (effect_status_retained h₁.1 h₁.2))

theorem old_writer_fenced_after_handoff (advanced : handoff before writer = some after) :
    writer ≠ after.writer := by
  unfold handoff at advanced
  split at advanced
  · rw [← Option.some.inj advanced]
    simp
  · contradiction

theorem stale_writer_cannot_revoke (stale : writer ≠ image.writer) :
    revoke image writer verified = none := by simp [revoke, stale]

theorem handoff_retains_oauth_lineage (advanced : handoff before writer = some after) :
    before.oauth.checkpoint.ledger.retains after.oauth.checkpoint.ledger := by
  unfold handoff at advanced
  split at advanced
  · cases advanced
    exact Refresh.Ledger.retains_refl _
  · contradiction

theorem revocation_retains_oauth_lineage (applied : revoke before writer verified = some after) :
    before.oauth.checkpoint.ledger.retains after.oauth.checkpoint.ledger := by
  unfold revoke at applied
  split at applied
  · cases next : before.oauth.revoke verified with
    | none => simp [next] at applied
    | some oauth =>
      have same : { before with oauth } = after := by simpa [next] using applied
      rw [← same]
      exact Recovery.persisted_revocation_retains_lineage next
  · contradiction

/-- A parsed inventory is structurally explicit and binds each operation key to
one exact retained intent. This does not authenticate or select the current head. -/
def restoreRetained (snapshot : Option (List (String × Retained))) : Option (List Retained) := do
  let rows ← snapshot
  if decide (rows.map Prod.fst).Nodup &&
      rows.all (fun row => !row.1.isEmpty && decide (row.1 = row.2.intent.operation)) then
    some (rows.map Prod.snd)
  else none

def retainedInventoryContract :
    Contract Unit (Option (List (String × Retained))) (List Retained) where
  input := ⟨"explicit-retained-operation-inventory", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"unique-operation-bound-retained-intents", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ snapshot result => restoreRetained snapshot = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareRetainedInventory (snapshot : Option (List (String × Retained))) :
    Except String (List Retained × Unit) :=
  match restoreRetained snapshot with
  | some retained => .ok (retained, ())
  | none => .error "Retained operation inventory refused"

theorem restored_inventory_exact (accepted : restoreRetained snapshot = some retained) :
    ∃ rows, snapshot = some rows ∧ (rows.map Prod.fst).Nodup ∧
      (∀ row ∈ rows, row.1 = row.2.intent.operation) ∧ retained = rows.map Prod.snd := by
  cases snapshot with
  | none => simp [restoreRetained] at accepted
  | some rows =>
    dsimp [restoreRetained] at accepted
    split at accepted
    next checked =>
      have ⟨unique, matched⟩ := Bool.and_eq_true_iff.mp checked
      exact ⟨rows, rfl, of_decide_eq_true unique,
        fun row member => of_decide_eq_true
          (Bool.and_eq_true_iff.mp (List.all_eq_true.mp matched row member)).2,
        (Option.some.inj accepted).symm⟩
    next => simp at accepted

theorem restored_inventory_unique (accepted : restoreRetained snapshot = some retained) :
    (retained.map (·.intent.operation)).Nodup := by
  obtain ⟨rows, _, unique, matched, rfl⟩ := restored_inventory_exact accepted
  have same : (rows.map Prod.snd).map (·.intent.operation) = rows.map Prod.fst := by
    simp only [List.map_map]
    exact List.map_congr_left (fun row member => (matched row member).symm)
  exact same.symm ▸ unique

theorem missing_inventory_refused : restoreRetained none = none := rfl

theorem repeated_inventory_key_refused (duplicate : ¬ (rows.map Prod.fst).Nodup) :
    restoreRetained (some rows) = none := by simp [restoreRetained, duplicate]

/-- A successful typed restore supplies uniqueness, not permission to execute. -/
theorem inventory_receipt_unique
    (receipt : Invocation retainedInventoryContract prepareRetainedInventory snapshot) :
    (receipt.result.map (·.intent.operation)).Nodup :=
  restored_inventory_unique receipt.logic

structure History where
  logKey : String
  entries : List CommitRef
  valid : Bool
  independent : Option Gateway.Lifecycle.WitnessFrontier

def History.current (history : History) : Bool :=
  history.valid &&
    decide (history.independent = some (Gateway.Lifecycle.WitnessFrontier.observe history.logKey history.entries))

structure BeginInput where
  image : Image
  writer : Nat
  checkedWriter : Nat
  read : ReplicaRead
  operation : String
  intent : CommitRef
  providerKey : String
  history : History
  receiver : Option ReceiverBinding := none

def begin (input : BeginInput) : Option Image := do
  let anchor ← input.history.independent
  if input.writer = input.image.writer ∧ input.checkedWriter = input.image.writer ∧
      input.operation ≠ "" ∧ input.operation = input.intent.operation ∧
      input.providerKey ≠ "" ∧ input.history.current = true ∧
      (input.history.entries.any fun entry => decide (entry = input.intent)) = true ∧
      (input.history.entries.filter fun entry => entry.operation == input.operation).length = 1 ∧
      ¬ (input.image.retained.any fun entry => entry.intent.operation == input.operation) = true then
    let oauth ← Recovery.finalize ⟨input.image.oauth.checkpoint.authorityId, some input.image.oauth, input.read⟩
    return { input.image with oauth, retained := ⟨input.intent, anchor, input.providerKey, input.receiver, false⟩ :: input.image.retained }
  else none

def beginContract : Contract Unit BeginInput Image where
  input := ⟨"current-writer-and-witnessed-OAuth-effect", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"persisted-OAuth-intent-before-observation", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => begin input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareBegin (input : BeginInput) : Except String (Image × Unit) :=
  match begin input with
  | some image => .ok (image, ())
  | none => .error "OAuth durable effect refused"

/-- Structural full-image equality in the model. The native pin pairs the
OAuth checkpoint with a commitment to proof reservations and effect records. -/
structure CurrentCommitInput where
  preparedGeneration : Nat
  actualGeneration : Nat
  envelope : Envelope
  actual : Current
  cedarAllowed : Bool
  independent : Image
  oauthTarget : Target
  request : BeginInput

def CurrentCommitInput.current (input : CurrentCommitInput) : Prop :=
  input.preparedGeneration = input.actualGeneration ∧
  input.independent = input.request.image ∧
  input.envelope.effect.operation = input.request.operation ∧
  input.envelope.effect.audience = input.oauthTarget.audience ∧
  input.oauthTarget = input.request.read.attempt.target ∧
  input.request.read.authority.now = input.actual.authority.now ∧
  accepts input.actual input.envelope input.cedarAllowed = true

instance (input : CurrentCommitInput) : Decidable input.current := by
  unfold CurrentCommitInput.current
  infer_instance

def CurrentCommitInput.reserve (input : CurrentCommitInput) : Option Image :=
  if input.current then begin input.request else none

def currentCommitContract : Contract Unit CurrentCommitInput Image where
  input := ⟨"current-Cedar-effect-and-independent-full-image", CurrentCommitInput.current,
    fun _ => inferInstance⟩
  output := ⟨"reserved-current-effect", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => input.reserve = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareCurrentCommit (input : CurrentCommitInput) : Except String (Image × Unit) :=
  match input.reserve with
  | some image => .ok (image, ())
  | none => .error "Current effect reservation refused"

theorem current_commit_rejects_stale_generation (input : CurrentCommitInput)
    (stale : input.preparedGeneration ≠ input.actualGeneration) : input.reserve = none := by
  simp [CurrentCommitInput.reserve, CurrentCommitInput.current, stale]

theorem current_commit_rejects_older_image (input : CurrentCommitInput)
    (older : input.independent ≠ input.request.image) : input.reserve = none := by
  simp [CurrentCommitInput.reserve, CurrentCommitInput.current, older]

theorem current_commit_binds_oauth_target
    (receipt : Invocation currentCommitContract prepareCurrentCommit input) :
    input.oauthTarget = input.request.read.attempt.target ∧
    input.request.read.authority.now = input.actual.authority.now := by
  have bound : input.current := receipt.input
  exact ⟨bound.2.2.2.2.1, bound.2.2.2.2.2.1⟩

theorem current_commit_uses_actual_begin
    (receipt : Invocation currentCommitContract prepareCurrentCommit input) :
    begin input.request = some receipt.result := by
  have accepted := receipt.logic
  change input.reserve = some receipt.result at accepted
  have current : input.current := receipt.input
  simpa [CurrentCommitInput.reserve, current] using accepted

theorem stale_writer_cannot_begin (input : BeginInput) (stale : input.writer ≠ input.image.writer) :
    begin input = none := by
  cases anchored : input.history.independent <;> simp [begin, anchored, stale]

theorem burned_operation_cannot_begin (input : BeginInput)
    (burned : (input.image.retained.any fun entry => entry.intent.operation == input.operation) = true) :
    begin input = none := by
  cases anchored : input.history.independent <;> simp [begin, anchored, burned]

theorem begin_records_burn (receipt : Invocation beginContract prepareBegin input) :
    (receipt.result.retained.any fun entry => entry.intent.operation == input.operation) = true := by
  have accepted := receipt.logic
  change begin input = some receipt.result at accepted
  cases anchored : input.history.independent with
  | none => simp [begin, anchored] at accepted
  | some anchor =>
    simp only [begin, anchored, bind, Option.bind] at accepted
    split at accepted
    · rename_i valid
      have operation := valid.2.2.2.1
      cases applied : Recovery.finalize
          ⟨input.image.oauth.checkpoint.authorityId, some input.image.oauth, input.read⟩ with
      | none => simp [applied] at accepted
      | some oauth =>
        simp [applied] at accepted
        rw [← accepted]
        simp [operation]
    · contradiction


/-- Fresh authorized work prepends one intent without deleting prior holds. -/
theorem begin_retained_shape (receipt : Invocation beginContract prepareBegin input) :
    ∃ entry, receipt.result.retained = entry :: input.image.retained ∧
      entry.intent.operation = input.operation ∧
      ¬ (input.image.retained.any fun prior =>
        prior.intent.operation == input.operation) = true := by
  have accepted := receipt.logic
  change begin input = some receipt.result at accepted
  cases anchored : input.history.independent with
  | none => simp [begin, anchored] at accepted
  | some anchor =>
    simp only [begin, anchored, bind, Option.bind] at accepted
    split at accepted
    · rename_i valid
      rcases valid with ⟨_, _, _, operation, _, _, _, _, fresh⟩
      cases applied : Recovery.finalize
          ⟨input.image.oauth.checkpoint.authorityId, some input.image.oauth, input.read⟩ with
      | none => simp [applied] at accepted
      | some oauth =>
        simp [applied] at accepted
        rw [← accepted]
        exact ⟨_, rfl, operation.symm, fresh⟩
    · contradiction

theorem begin_preserves_prior_burn (receipt : Invocation beginContract prepareBegin input)
    (burned : (input.image.retained.any fun entry => entry.intent.operation == operation) = true) :
    (receipt.result.retained.any fun entry => entry.intent.operation == operation) = true := by
  obtain ⟨_, retained, _, _⟩ := begin_retained_shape receipt
  simp [retained, burned]

theorem begin_preserves_operation_uniqueness (receipt : Invocation beginContract prepareBegin input)
    (unique : (input.image.retained.map (·.intent.operation)).Nodup) :
    (receipt.result.retained.map (·.intent.operation)).Nodup := by
  obtain ⟨entry, retained, operation, fresh⟩ := begin_retained_shape receipt
  rw [retained, List.map_cons, List.nodup_cons]
  refine ⟨?_, unique⟩
  intro member
  obtain ⟨prior, known, same⟩ := List.mem_map.mp member
  apply fresh
  apply List.any_eq_true.mpr
  exact ⟨prior, known, by simpa [operation] using same⟩

/-- Actual effect reservation updates replay/intent state while keeping the
independently recovered OAuth token/family checkpoint unchanged. -/
theorem begin_retains_oauth_checkpoint (receipt : Invocation beginContract prepareBegin input) :
    receipt.result.oauth.checkpoint = input.image.oauth.checkpoint := by
  have accepted := receipt.logic
  change begin input = some receipt.result at accepted
  cases anchored : input.history.independent with
  | none => simp [begin, anchored] at accepted
  | some anchor =>
    simp only [begin, anchored, bind, Option.bind] at accepted
    split at accepted
    · cases applied : Recovery.finalize
          ⟨input.image.oauth.checkpoint.authorityId, some input.image.oauth, input.read⟩ with
      | none => simp [applied] at accepted
      | some oauth =>
        simp [applied] at accepted
        rw [← accepted]
        exact Recovery.final_retains_original_checkpoint applied rfl
    · contradiction

structure ReconcileInput where
  image : Image
  writer : Nat
  operation : String
  trust : ProviderAuditTrust
  source : CedarPooSpec.ZeroTrust.FactAuthority String String
  history : History
  actions : List AuditRecord
  outcomes : List ProviderOutcome

def ReconcileInput.retained (input : ReconcileInput) : Option Retained :=
  match input.image.retained.filter (fun entry => entry.intent.operation == input.operation) with
  | [entry] => some entry
  | _ => none

def ReconcileInput.outcome (input : ReconcileInput) (entry : Retained)
    (observation : Option ReceiverObservation := none) : Option ProviderOutcome :=
  input.outcomes.find? fun outcome =>
    !entry.legacy && decide (outcome.receipt.commit = entry.intent) &&
      decide (entry.receiver = observation.map (·.binding)) &&
      observation.all (fun source => decide (outcome = source.outcome))

def Image.settledOutcome (image : Image) (operation : String) : Option ProviderOutcome :=
  image.resolved.find? (fun outcome => outcome.receipt.commit.operation == operation)

def Image.settle (image : Image) (outcome : ProviderOutcome) : Option Image :=
  match image.settledOutcome outcome.receipt.commit.operation with
  | none => some { image with resolved := outcome :: image.resolved }
  | some prior => if prior = outcome then some image else none

theorem settlement_preserves_authority {image after : Image} (applied : image.settle outcome = some after) :
    after.oauth = image.oauth ∧ after.writer = image.writer ∧ after.retained = image.retained := by
  unfold Image.settle at applied
  split at applied
  · cases applied
    exact ⟨rfl, rfl, rfl⟩
  · split at applied
    · cases applied
      exact ⟨rfl, rfl, rfl⟩
    · contradiction

theorem settlement_pins_outcome {image after : Image} (applied : image.settle outcome = some after) :
    after.settledOutcome outcome.receipt.commit.operation = some outcome := by
  unfold Image.settle at applied
  split at applied
  · cases applied
    simp [Image.settledOutcome]
  · rename_i prior pinned
    split at applied
    · rename_i equal
      cases applied
      simpa [equal] using pinned
    · contradiction

theorem pinned_outcome_is_idempotent {image : Image}
    (pinned : image.settledOutcome outcome.receipt.commit.operation = some outcome) :
    image.settle outcome = some image := by
  simp [Image.settle, pinned]

def reconcileFrom (input : ReconcileInput) (observation : Option ReceiverObservation) : Option Image := do
  let entry ← input.retained
  if input.writer = input.image.writer ∧ input.trust.providerKey = entry.providerKey ∧
      input.trust.logKey = input.history.logKey ∧ input.history.current = true ∧
      entry.anchor.extends input.history.logKey input.history.entries = true ∧
      (reconcileProviderIntent input.trust input.source entry.intent input.actions input.outcomes
        input.history.valid input.history.entries).clean = true then
    let outcome ← input.outcome entry observation
    input.image.settle outcome
  else none

def reconcile (input : ReconcileInput) : Option Image := reconcileFrom input none

theorem reconciliation_from_pins_committed_outcome
    (applied : reconcileFrom input (some observation) = some after) :
    after.settledOutcome observation.outcome.receipt.commit.operation = some observation.outcome := by
  cases found : input.retained with
  | none => simp [reconcileFrom, found] at applied
  | some entry =>
    simp only [reconcileFrom, found, bind, Option.bind] at applied
    split at applied
    · cases selected : input.outcome entry (some observation) with
      | none => simp [selected] at applied
      | some outcome =>
        have settled : input.image.settle outcome = some after := by simpa [selected] using applied
        unfold ReconcileInput.outcome at selected
        have exactMatch := List.find?_some selected
        simp [Bool.and_eq_true, and_assoc] at exactMatch
        simpa [exactMatch.2.2.2] using settlement_pins_outcome settled
    · contradiction

theorem missing_committed_outcome_refuses_recovery (input : ReconcileInput)
    (observation : ReceiverObservation) (missing : observation.outcome ∉ input.outcomes) :
    reconcileFrom input (some observation) = none := by
  cases found : input.retained with
  | none => simp [reconcileFrom, found]
  | some entry =>
    have absent : input.outcome entry (some observation) = none := by
      apply List.find?_eq_none.mpr
      intro outcome member
      have different : outcome ≠ observation.outcome := fun equal => missing (equal ▸ member)
      simp [different]
    simp [reconcileFrom, found, absent]

def reconcileContract : Contract Unit ReconcileInput Image where
  input := ⟨"retained-intent-and-independent-provider-audit", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"settlement-without-OAuth-or-intent-reopening", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => reconcile input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareReconcile (input : ReconcileInput) : Except String (Image × Unit) :=
  match reconcile input with
  | some image => .ok (image, ())
  | none => .error "OAuth effect remains unresolved"

theorem reconciliation_from_preserves_authority
    (accepted : reconcileFrom input observation = some after) :
    after.oauth = input.image.oauth ∧ after.writer = input.image.writer ∧
      after.retained = input.image.retained := by
  cases found : input.retained with
  | none => simp [reconcileFrom, found] at accepted
  | some entry =>
    simp only [reconcileFrom, found, bind, Option.bind] at accepted
    split at accepted
    · cases observed : input.outcome entry observation with
      | none => simp [observed] at accepted
      | some outcome =>
        exact settlement_preserves_authority (by simpa [observed] using accepted)
    · contradiction

theorem reconciliation_preserves_burn_and_revocations
    (receipt : Invocation reconcileContract prepareReconcile input) :
    receipt.result.oauth = input.image.oauth ∧ receipt.result.writer = input.image.writer ∧
      receipt.result.retained = input.image.retained :=
  reconciliation_from_preserves_authority receipt.logic

theorem reconciliation_pins_outcome
    (receipt : Invocation reconcileContract prepareReconcile input)
    (found : input.retained = some entry) (observed : input.outcome entry = some outcome) :
    receipt.result.settledOutcome outcome.receipt.commit.operation = some outcome := by
  have accepted := receipt.logic
  change reconcile input = some receipt.result at accepted
  simp only [reconcile, reconcileFrom, found, bind, Option.bind] at accepted
  split at accepted
  · exact settlement_pins_outcome (by simpa [observed] using accepted)
  · contradiction

theorem conflicting_outcome_cannot_replace_settlement (found : input.retained = some entry)
    (observed : input.outcome entry = some outcome)
    (pinned : input.image.settledOutcome outcome.receipt.commit.operation = some prior)
    (different : prior ≠ outcome) : reconcile input = none := by
  simp [reconcile, reconcileFrom, found, observed, Image.settle, pinned, different]

/-- The authority serializes contenders. The losing worker sees the
winner's committed image even if the winner never received its acknowledgment. -/
theorem serialized_conflict_cannot_win
    (winner : Invocation reconcileContract prepareReconcile input)
    (found : input.retained = some entry) (selected : input.outcome entry = some accepted)
    (loser : ReconcileInput) (current : loser.image = recoverImage .durable input.image winner.result)
    (loserFound : loser.retained = some other) (candidate : loser.outcome other = some conflicting)
    (same : conflicting.receipt.commit.operation = accepted.receipt.commit.operation)
    (different : accepted ≠ conflicting) : reconcile loser = none := by
  apply conflicting_outcome_cannot_replace_settlement loserFound candidate _ different
  rw [current, same]
  exact reconciliation_pins_outcome winner found selected

theorem committed_settlement_survives_recovery
    (receipt : Invocation reconcileContract prepareReconcile input)
    (found : input.retained = some entry) (selected : input.outcome entry = some outcome)
    (first : handoff (recoverImage .durable input.image receipt.result) writer = some standby)
    (revoked : revoke standby standbyWriter verified = some revokedImage)
    (second : handoff revokedImage standbyWriter = some after) :
    after.settledOutcome outcome.receipt.commit.operation = some outcome ∧
      after.settle outcome = some after := by
  have preserved := (handoff_preserves_effect_state second).2.trans
    ((revocation_preserves_effect_state revoked).2.trans (handoff_preserves_effect_state first).2)
  have pinned : after.settledOutcome outcome.receipt.commit.operation = some outcome := by
    simpa only [Image.settledOutcome, preserved, recoverImage] using
      reconciliation_pins_outcome receipt found selected
  exact ⟨pinned, pinned_outcome_is_idempotent pinned⟩

theorem settlement_cannot_reopen_operation
    (receipt : Invocation reconcileContract prepareReconcile input) (retry : BeginInput)
    (burned : (input.image.retained.any fun entry => entry.intent.operation == retry.operation) = true) :
    begin { retry with image := receipt.result } = none := by
  apply burned_operation_cannot_begin
  simpa only [(reconciliation_preserves_burn_and_revocations receipt).2.2] using burned

theorem unclean_evidence_cannot_settle (found : input.retained = some entry)
    (unclean : (reconcileProviderIntent input.trust input.source entry.intent input.actions input.outcomes
      input.history.valid input.history.entries).clean = false) : reconcile input = none := by
  simp [reconcile, reconcileFrom, found, unclean]

theorem missing_outcome_cannot_settle (found : input.retained = some entry)
    (logged : entry.intent ∈ input.history.entries) (absent : input.outcomes = []) :
    reconcile input = none := by
  apply unclean_evidence_cannot_settle found
  rw [absent]
  exact scoped_missing_outcome_is_unclean _ _ _ _ _ _ logged

def Retained.bindLegacy (entry : Retained) (operation : String) (binding : ReceiverBinding) : Retained :=
  if entry.intent.operation = operation then { entry with receiver := some binding, legacy := false }
  else entry

@[simp] theorem Retained.bindLegacy_preserves_intent (entry : Retained)
    (operation : String) (binding : ReceiverBinding) :
    (entry.bindLegacy operation binding).intent = entry.intent := by
  simp [Retained.bindLegacy]
  split <;> rfl

def ReconcileInput.bindLegacy (input : ReconcileInput) (binding : ReceiverBinding) : ReconcileInput :=
  { input with image := { input.image with
      retained := input.image.retained.map (fun entry => entry.bindLegacy input.operation binding) } }

/-- The tentative binding is part of the result only when the exact
committed receipt independently reconciles. -/
def migrateFrom (input : ReconcileInput) (observation : ReceiverObservation) : Option Image := do
  let entry ← input.retained
  if entry.legacy = true ∧ entry.receiver = none ∧ input.image.settledOutcome input.operation = none then
    reconcileFrom (input.bindLegacy observation.binding) (some observation)
  else if entry.receiver = some observation.binding ∧ (input.image.settledOutcome input.operation).isSome then
    reconcileFrom input (some observation)
  else none

/-- Explicit settled-record migration still uses the retained intent, pinned
audit roots and independently selected receiver outcome. -/
def migrateSettledFrom (input : ReconcileInput) (observation : ReceiverObservation) : Option Image := do
  let entry ← input.retained
  if (input.image.settledOutcome input.operation).isSome ∧
      ((entry.legacy = true ∧ entry.receiver = none) ∨ entry.receiver = some observation.binding) then
    reconcileFrom (input.bindLegacy observation.binding) (some observation)
  else none

theorem settled_migration_requires_prior_completion
    (applied : migrateSettledFrom input observation = some after) :
    (input.image.settledOutcome input.operation).isSome = true := by
  cases found : input.retained with
  | none => simp [migrateSettledFrom, found] at applied
  | some entry =>
    simp only [migrateSettledFrom, found, bind, Option.bind] at applied
    split at applied
    · rename_i qualified
      exact qualified.1
    · contradiction

theorem settled_migration_missing_receipt_refused
    (missing : observation.outcome ∉ input.outcomes) :
    migrateSettledFrom input observation = none := by
  have refused := missing_committed_outcome_refuses_recovery
    (input.bindLegacy observation.binding) observation missing
  cases found : input.retained <;> simp [migrateSettledFrom, found, refused]

theorem settled_migration_detached_refused (found : input.retained = some entry)
    (detached : entry.receiver = none) (notLegacy : entry.legacy = false) :
    migrateSettledFrom input observation = none := by
  simp [migrateSettledFrom, found, detached, notLegacy]

theorem settled_migration_preserves_authority_and_burn
    (applied : migrateSettledFrom input observation = some after) (operation : String) :
    after.oauth = input.image.oauth ∧ after.writer = input.image.writer ∧
      (after.retained.any fun entry => entry.intent.operation == operation) =
        (input.image.retained.any fun entry => entry.intent.operation == operation) := by
  cases found : input.retained with
  | none => simp [migrateSettledFrom, found] at applied
  | some entry =>
    simp only [migrateSettledFrom, found, bind, Option.bind] at applied
    split at applied
    · have preserved := reconciliation_from_preserves_authority applied
      refine ⟨preserved.1, preserved.2.1, ?_⟩
      rw [preserved.2.2]
      simp [ReconcileInput.bindLegacy, List.any_map, Function.comp_def]
    · contradiction

theorem migration_preserves_authority_and_burn
    (applied : migrateFrom input observation = some after) (operation : String) :
    after.oauth = input.image.oauth ∧ after.writer = input.image.writer ∧
      (after.retained.any fun entry => entry.intent.operation == operation) =
        (input.image.retained.any fun entry => entry.intent.operation == operation) := by
  cases found : input.retained with
  | none => simp [migrateFrom, found] at applied
  | some entry =>
    simp only [migrateFrom, found, bind, Option.bind] at applied
    split at applied
    · have preserved := reconciliation_from_preserves_authority applied
      refine ⟨preserved.1, preserved.2.1, ?_⟩
      rw [preserved.2.2]
      simp [ReconcileInput.bindLegacy, List.any_map, Function.comp_def]
    · split at applied
      · have preserved := reconciliation_from_preserves_authority applied
        exact ⟨preserved.1, preserved.2.1, by rw [preserved.2.2]⟩
      · contradiction

theorem migration_pins_committed_outcome
    (applied : migrateFrom input observation = some after) :
    after.settledOutcome observation.outcome.receipt.commit.operation = some observation.outcome := by
  cases found : input.retained with
  | none => simp [migrateFrom, found] at applied
  | some entry =>
    simp only [migrateFrom, found, bind, Option.bind] at applied
    split at applied
    · exact reconciliation_from_pins_committed_outcome applied
    · split at applied
      · exact reconciliation_from_pins_committed_outcome applied
      · contradiction

/-- A staged migration leaves the original operation reserved after
takeover and revocation, even when the worker lost its evidence. -/
theorem staged_migration_cannot_reopen_operation (before staged : Image) (retry : BeginInput)
    (takeover : handoff (recoverImage .staged before staged) writer = some successor)
    (revoked : revoke successor currentWriter verified = some after)
    (burned : (before.retained.any fun entry => entry.intent.operation == retry.operation) = true) :
    begin { retry with image := after } = none := by
  apply burned_operation_cannot_begin
  simpa only [(revocation_preserves_effect_state revoked).1,
    (handoff_preserves_effect_state takeover).1, recoverImage] using burned

/-- A durable migration retains its independently committed receipt when
the writer crashes before acknowledgment and its successor revokes the grant. -/
theorem committed_migration_survives_takeover
    (applied : migrateFrom input observation = some committed)
    (takeover : handoff (recoverImage .durable input.image committed) writer = some successor)
    (revoked : revoke successor currentWriter verified = some after) :
    after.settledOutcome observation.outcome.receipt.commit.operation = some observation.outcome := by
  simpa only [Image.settledOutcome, (revocation_preserves_effect_state revoked).2,
    (handoff_preserves_effect_state takeover).2, recoverImage] using
      migration_pins_committed_outcome applied

theorem committed_migration_cannot_reopen_after_failover (retry : BeginInput)
    (applied : migrateFrom input observation = some committed)
    (first : handoff committed writer = some successor)
    (revoked : revoke successor successorWriter verified = some revokedImage)
    (second : handoff revokedImage successorWriter = some after)
    (burned : (input.image.retained.any fun entry => entry.intent.operation == retry.operation) = true) :
    begin { retry with image := after } = none := by
  apply burned_operation_cannot_begin
  simpa only [(handoff_preserves_effect_state second).1, (revocation_preserves_effect_state revoked).1,
    (handoff_preserves_effect_state first).1, (migration_preserves_authority_and_burn applied retry.operation).2.2]
    using burned

/-- Re-auditing the independently committed receipt after settlement cannot
rewrite the durable image, even under a different current writer. -/
theorem confirmed_migration_is_read_only
    (pinned : input.image.settledOutcome observation.outcome.receipt.commit.operation =
      some observation.outcome)
    (sameOperation : input.operation = observation.outcome.receipt.commit.operation)
    (applied : migrateFrom input observation = some after) : after = input.image := by
  have settled : input.image.settledOutcome input.operation = some observation.outcome :=
    sameOperation ▸ pinned
  cases found : input.retained with
  | none => simp [migrateFrom, found] at applied
  | some entry =>
    simp only [migrateFrom, found, bind, Option.bind, settled, reduceCtorEq,
      and_false, Option.isSome_some, and_true, ite_false] at applied
    split at applied
    · simp only [reconcileFrom, found, bind, Option.bind] at applied
      split at applied
      · cases selected : input.outcome entry (some observation) with
        | none => simp [selected] at applied
        | some outcome =>
          have exactMatch := List.find?_some selected
          simp [Bool.and_eq_true, and_assoc] at exactMatch
          simpa [selected, exactMatch.2.2.2, pinned_outcome_is_idempotent pinned, eq_comm] using applied
      · contradiction
    · contradiction

theorem missing_committed_outcome_refuses_migration (input : ReconcileInput)
    (observation : ReceiverObservation) (missing : observation.outcome ∉ input.outcomes) :
    migrateFrom input observation = none := by
  cases found : input.retained with
  | none => simp [migrateFrom, found]
  | some entry =>
    have unchanged : (input.bindLegacy observation.binding).outcomes = input.outcomes := rfl
    simp [migrateFrom, found,
      missing_committed_outcome_refuses_recovery (input.bindLegacy observation.binding)
        observation (unchanged.symm ▸ missing),
      missing_committed_outcome_refuses_recovery input observation missing]

theorem reconciliation_refuses_retired_writer (input : ReconcileInput)
    (observation : Option ReceiverObservation) (stale : input.writer ≠ input.image.writer) :
    reconcileFrom input observation = none := by
  cases found : input.retained <;> simp [reconcileFrom, found, stale]

theorem migration_refuses_retired_writer (input : ReconcileInput)
    (observation : ReceiverObservation) (stale : input.writer ≠ input.image.writer) :
    migrateFrom input observation = none := by
  cases found : input.retained with
  | none => simp [migrateFrom, found]
  | some entry =>
    have bound := reconciliation_refuses_retired_writer
      (input.bindLegacy observation.binding) (some observation) stale
    simp [migrateFrom, found, bound, reconciliation_refuses_retired_writer input (some observation) stale]

theorem restored_inventory_burns_operation
    (accepted : restoreRetained (some rows) = some retained)
    (member : (operation, entry) ∈ rows) :
    (retained.any fun item => item.intent.operation == operation) = true := by
  obtain ⟨actual, same, _, matched, contents⟩ := restored_inventory_exact accepted
  have sameRows : actual = rows := Option.some.inj same.symm
  subst actual
  rw [contents]
  apply List.any_eq_true.mpr
  exact ⟨entry, List.mem_map.mpr ⟨(operation, entry), member, rfl⟩,
    by simpa using (matched (operation, entry) member).symm⟩

theorem restored_inventory_cannot_begin {image : Image} {retry : BeginInput}
    (receipt : Invocation retainedInventoryContract prepareRetainedInventory (some rows))
    (member : (retry.operation, entry) ∈ rows)
    (retained : image.retained = receipt.result) :
    begin { retry with image := image } = none := by
  apply burned_operation_cannot_begin
  rw [retained]
  exact restored_inventory_burns_operation receipt.logic member

end CedarPooSpec.Gateway.OAuth.Revocation.Crash
