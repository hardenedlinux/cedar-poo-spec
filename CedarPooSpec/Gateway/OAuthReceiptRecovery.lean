import CedarPooSpec.Gateway.OAuthReceiptIdentity

/-! The mapping and the OAuth settlement share one recoverable commit image.
An acknowledged mapping is immutable, including across ownership changes. -/
namespace CedarPooSpec.Gateway.OAuth.ReceiptRecovery
open ReceiptIdentity LeanPoo.Functional.DeclarativeMetadata

structure Stored where
  identity : ReceiptIdentity.Identity
  intentSource : SignedSource
  outcomeSource : SignedSource
  symbolic : Gateway.EffectProtocol.ProviderOutcome
  deriving DecidableEq

def Request.stored (request : Request) : Stored :=
  ⟨request.identity, request.intentSource, request.outcomeSource, request.symbolic⟩

def lookup (rows : List Stored) (operation : String) : Option Stored :=
  rows.find? (fun row => row.identity.operation == operation)

def record (rows : List Stored) (row : Stored) : Option (List Stored) :=
  match lookup rows row.identity.operation with
  | some prior => if prior = row then some rows else none
  | none => some (row :: rows)

theorem record_idempotent (bound : lookup rows row.identity.operation = some row) :
    record rows row = some rows := by simp [record, bound]

theorem record_rejects_replacement (bound : lookup rows row.identity.operation = some prior)
    (different : prior ≠ row) : record rows row = none := by simp [record, bound, different]

theorem record_binds (accepted : record rows row = some after) :
    lookup after row.identity.operation = some row := by
  unfold record at accepted
  cases found : lookup rows row.identity.operation with
  | none =>
    simp [found] at accepted
    subst after
    simp [lookup]
  | some prior =>
    simp only [found] at accepted
    split at accepted
    · rename_i same
      simp only [Option.some.injEq] at accepted
      subst after
      simpa [same] using found
    · contradiction

theorem record_preserves (bound : lookup rows operation = some prior)
    (accepted : record rows row = some after) : lookup after operation = some prior := by
  unfold record at accepted
  cases found : lookup rows row.identity.operation with
  | none =>
    have different : row.identity.operation ≠ operation := by
      intro same
      simp [same, bound] at found
    simp [found] at accepted
    subst after
    simpa [lookup, different] using bound
  | some old =>
    simp only [found] at accepted
    split at accepted
    · have same := Option.some.inj accepted
      rw [← same]
      exact bound
    · contradiction

structure Image where
  oauth : Revocation.Crash.Image
  rows : List Stored := []
  deriving DecidableEq

structure Input where
  image : Image
  writer : Nat
  authority : ReceiptIdentity.Authority
  request : Request
  recovery : Receiver.ManagedReconciliation

def checkedImage (input : Input) : Option Revocation.Crash.Image := do
  if input.writer ≠ input.image.oauth.writer ∨
      input.request.operation ≠ input.recovery.audit.operation ∨
      input.authority.providerKey ≠ input.recovery.audit.trust.providerKey ∨
      input.authority.witnessKey ≠ input.recovery.audit.trust.logKey then none else do
  let _ ← resolve input.authority input.request
  if (lookup input.image.rows input.request.operation).isNone &&
      Revocation.Crash.effectStatus input.image.oauth input.request.operation != .unresolved then none else do
  let current := { input.recovery with audit :=
    { input.recovery.audit with image := input.image.oauth, writer := input.writer } }
  let next ← Receiver.migrateLegacy ⟨current, input.authority.receiver⟩
  if next.settledOutcome input.request.operation = some input.request.symbolic then some next else none

def persist (input : Input) : Option Image := do
  let image ← checkedImage input
  let rows ← record input.image.rows (Request.stored input.request)
  return ⟨image, rows⟩

def contract : Contract Unit Input Image where
  input := ⟨"current-writer-and-independent-receiver-receipt", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"atomic-settlement-and-exact-receipt-mapping", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => persist input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : Input) : Except String (Image × Unit) :=
  match persist input with
  | some result => .ok (result, ())
  | none => .error "durable receipt mapping refused"

theorem stale_writer_refused (stale : input.writer ≠ input.image.oauth.writer) :
    persist input = none := by simp [persist, checkedImage, stale]

theorem mismatched_audit_root_refused
    (wrong : input.authority.providerKey ≠ input.recovery.audit.trust.providerKey ∨
      input.authority.witnessKey ≠ input.recovery.audit.trust.logKey) :
    persist input = none := by
  rcases wrong with provider | witness
  · simp [persist, checkedImage, provider]
  · simp [persist, checkedImage, witness]

theorem replacement_refused
    (bound : lookup input.image.rows input.request.identity.operation = some prior)
    (different : prior ≠ Request.stored input.request) : persist input = none := by
  have refused := record_rejects_replacement bound different
  cases checked : checkedImage input <;> simp [persist, checked, refused]

theorem persistence_records (receipt : Invocation contract prepare input) :
    lookup receipt.result.rows input.request.identity.operation = some (Request.stored input.request) := by
  have accepted := receipt.logic
  change persist input = some receipt.result at accepted
  cases checked : checkedImage input with
  | none => simp [persist, checked] at accepted
  | some image =>
    cases stored : record input.image.rows (Request.stored input.request) with
    | none => simp [persist, checked, stored] at accepted
    | some rows =>
      have same : receipt.result = ⟨image, rows⟩ := by
        simpa [persist, checked, stored] using accepted.symm
      rw [same]
      exact record_binds stored

theorem persistence_keeps_original (receipt : Invocation contract prepare input)
    (bound : lookup input.image.rows operation = some prior) :
    lookup receipt.result.rows operation = some prior := by
  have accepted := receipt.logic
  change persist input = some receipt.result at accepted
  cases checked : checkedImage input with
  | none => simp [persist, checked] at accepted
  | some image =>
    cases stored : record input.image.rows (Request.stored input.request) with
    | none => simp [persist, checked, stored] at accepted
    | some rows =>
      have same : receipt.result = ⟨image, rows⟩ := by
        simpa [persist, checked, stored] using accepted.symm
      rw [same]
      exact record_preserves bound stored

theorem staged_mapping_not_recovered (before after : Image) :
    (Revocation.Crash.recoverImage .staged before after).rows = before.rows := rfl

theorem durable_mapping_recovers_without_ack (receipt : Invocation contract prepare input) :
    lookup (Revocation.Crash.recoverImage .durable input.image receipt.result).rows
      input.request.identity.operation = some (Request.stored input.request) :=
  persistence_records receipt

inductive Trace : Image → Image → Prop where
  | start (image) : Trace image image
  | authorization (prior : Trace initial before)
      (history : Receiver.LegacyRecoveryTrace before.oauth after) :
      Trace initial { before with oauth := after }
  | commit (prior : Trace initial before)
      (receipt : Invocation contract prepare input) (current : input.image = before)
      (boundary : Revocation.Crash.CommitBoundary) :
      Trace initial (Revocation.Crash.recoverImage boundary before receipt.result)

theorem trace_preserves_original (history : Trace initial after)
    (bound : lookup initial.rows operation = some prior) :
    lookup after.rows operation = some prior := by
  induction history with
  | start => exact bound
  | authorization _ _ ih => exact ih
  | commit _ receipt current boundary ih =>
    cases boundary with
    | staged => exact ih
    | durable => exact persistence_keeps_original receipt (by simpa [current] using ih)

end CedarPooSpec.Gateway.OAuth.ReceiptRecovery
