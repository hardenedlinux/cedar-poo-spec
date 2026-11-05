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
    return { input.image with oauth, retained := ⟨input.intent, anchor, input.providerKey, input.receiver⟩ :: input.image.retained }
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
    decide (outcome.receipt.commit = entry.intent) &&
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
        simpa [exactMatch.2.2] using settlement_pins_outcome settled
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

theorem reconciliation_preserves_burn_and_revocations
    (receipt : Invocation reconcileContract prepareReconcile input) :
    receipt.result.oauth = input.image.oauth ∧ receipt.result.writer = input.image.writer ∧
    receipt.result.retained = input.image.retained := by
  have accepted := receipt.logic
  change reconcile input = some receipt.result at accepted
  cases found : input.retained with
  | none => simp [reconcile, reconcileFrom, found] at accepted
  | some entry =>
    simp only [reconcile, reconcileFrom, found, bind, Option.bind] at accepted
    split at accepted
    · cases observed : input.outcome entry with
      | none => simp [observed] at accepted
      | some outcome =>
        exact settlement_preserves_authority (by simpa [observed] using accepted)
    · contradiction

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

end CedarPooSpec.Gateway.OAuth.Revocation.Crash
