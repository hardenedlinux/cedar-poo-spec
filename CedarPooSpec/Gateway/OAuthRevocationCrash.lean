import CedarPooSpec.Gateway.OAuthRevocationRecovery
import CedarPooSpec.Gateway.Lifecycle

/-! Crash recovery keeps writer fencing, the OAuth proof reservation and the
exact effect intent in one authority-owned image. The provider supplies
independent completion evidence. Recovery never authorizes a new send. -/
namespace CedarPooSpec.Gateway.OAuth.Revocation.Crash
open Gateway.EffectProtocol LeanPoo.Functional.DeclarativeMetadata

structure Retained where
  intent : CommitRef
  anchor : Gateway.Lifecycle.WitnessFrontier
  providerKey : String
  deriving DecidableEq

structure Image where
  oauth : Recovery.Store
  writer : Nat := 0
  retained : List Retained := []
  resolved : List CommitRef := []
  deriving DecidableEq

inductive CommitBoundary where
  | staged
  | durable

/-- A staged write cannot be recovered as a committed image. The durable
image survives even if the acknowledgment was lost. -/
def recoverImage (boundary : CommitBoundary) (before after : Image) : Image :=
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

def begin (input : BeginInput) : Option Image := do
  let anchor ← input.history.independent
  if input.writer = input.image.writer ∧ input.checkedWriter = input.image.writer ∧
      input.operation ≠ "" ∧ input.operation = input.intent.operation ∧
      input.providerKey ≠ "" ∧ input.history.current = true ∧
      (input.history.entries.any fun entry => decide (entry = input.intent)) = true ∧
      (input.history.entries.filter fun entry => entry.operation == input.operation).length = 1 ∧
      ¬ (input.image.retained.any fun entry => entry.intent.operation == input.operation) = true then
    let oauth ← Recovery.finalize ⟨input.image.oauth.checkpoint.authorityId, some input.image.oauth, input.read⟩
    return { input.image with oauth, retained := ⟨input.intent, anchor, input.providerKey⟩ :: input.image.retained }
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

def reconcile (input : ReconcileInput) : Option Image := do
  let entry ← input.retained
  if input.writer = input.image.writer ∧ input.trust.providerKey = entry.providerKey ∧
      input.trust.logKey = input.history.logKey ∧ input.history.current = true ∧
      entry.anchor.extends input.history.logKey input.history.entries = true ∧
      (reconcileProviderIntent input.trust input.source entry.intent input.actions input.outcomes
        input.history.valid input.history.entries).clean = true then
    return { input.image with resolved :=
      if input.image.resolved.any (fun prior => decide (prior = entry.intent)) then input.image.resolved else entry.intent :: input.image.resolved }
  else none

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
  | none => simp [reconcile, found] at accepted
  | some entry =>
    simp only [reconcile, found, bind, Option.bind] at accepted
    split at accepted
    · rw [← Option.some.inj accepted]
      exact ⟨rfl, rfl, rfl⟩
    · contradiction

theorem settlement_cannot_reopen_operation
    (receipt : Invocation reconcileContract prepareReconcile input) (retry : BeginInput)
    (burned : (input.image.retained.any fun entry => entry.intent.operation == retry.operation) = true) :
    begin { retry with image := receipt.result } = none := by
  apply burned_operation_cannot_begin
  simpa only [(reconciliation_preserves_burn_and_revocations receipt).2.2] using burned

theorem unclean_evidence_cannot_settle (found : input.retained = some entry)
    (unclean : (reconcileProviderIntent input.trust input.source entry.intent input.actions input.outcomes
      input.history.valid input.history.entries).clean = false) : reconcile input = none := by
  simp [reconcile, found, unclean]

end CedarPooSpec.Gateway.OAuth.Revocation.Crash
