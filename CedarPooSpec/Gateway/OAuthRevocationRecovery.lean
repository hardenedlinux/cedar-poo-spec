import CedarPooSpec.Gateway.OAuthRevocation

/-! The independently persisted image holds the revocation checkpoint and
the resource proof reservations. Recovery never adopts a replica as authority.
The Host serializes final use and revoke against this durable image. -/
namespace CedarPooSpec.Gateway.OAuth.Revocation.Recovery
open LeanPoo.Functional.DeclarativeMetadata

structure Store where
  checkpoint : Checkpoint
  reserved : List ProofKey := []
  deriving DecidableEq

structure RecoveryInput where
  authorityId : String
  durable : Option Store
  replica : Checkpoint

def recover (input : RecoveryInput) : Option Store := do
  let store ← input.durable
  if input.authorityId ≠ "" ∧ store.checkpoint.authorityId = input.authorityId ∧
      input.replica = store.checkpoint then some store else none

def recoveryContract : Contract Unit RecoveryInput Store where
  input := ⟨"independent-durable-OAuth-state-and-replica", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"exact-recovered-OAuth-store", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => recover input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareRecovery (input : RecoveryInput) : Except String (Store × Unit) :=
  match recover input with
  | some store => .ok (store, ())
  | none => .error "OAuth recovery refused"

theorem recovery_retains_independent_store (accepted : recover input = some store) :
    input.durable = some store ∧ input.replica = store.checkpoint ∧
    input.authorityId = store.checkpoint.authorityId := by
  cases present : input.durable with
  | none => simp [recover, present] at accepted
  | some actual =>
    simp only [recover, present, bind, Option.bind] at accepted
    split at accepted
    · rename_i valid
      cases accepted
      exact ⟨rfl, valid.2.2, valid.2.1.symm⟩
    · contradiction

theorem stale_replica_cannot_recover (present : input.durable = some store)
    (different : input.replica ≠ store.checkpoint) : recover input = none := by
  simp [recover, present, different]

def Store.install (store : Store) (ledger : Refresh.Ledger) : Store :=
  if ledger = store.checkpoint.ledger then store
  else { store with checkpoint := { store.checkpoint with
    position := store.checkpoint.position + 1, ledger := ledger } }

theorem Store.install_ledger (store : Store) (ledger : Refresh.Ledger) :
    (store.install ledger).checkpoint.ledger = ledger := by
  unfold Store.install
  split
  · rename_i unchanged
    exact unchanged.symm
  · rfl

/-- Use the authenticated family revocation transition and advance the
position only when the ledger contents change. -/
def Store.revoke (store : Store) (verified : PAR.VerifiedClient Refresh.RefreshDigest) : Option Store :=
  (Refresh.revoke ⟨store.checkpoint.ledger, verified⟩).map store.install

theorem persisted_revocation_marks_family {store next : Store}
    (applied : store.revoke verified = some next) :
    (Refresh.RevocationInput.key ⟨store.checkpoint.ledger, verified⟩) ∈ next.checkpoint.ledger.revoked := by
  let input : Refresh.RevocationInput := ⟨store.checkpoint.ledger, verified⟩
  change (Refresh.revoke input).map store.install = some next at applied
  cases revoked : Refresh.revoke input with
  | none => simp [revoked] at applied
  | some ledger =>
    have successor : store.install ledger = next := by
      simpa [revoked] using applied
    let receipt : Invocation Refresh.revokeContract Refresh.prepareRevoke input :=
      ⟨ledger, (), by simp [Refresh.prepareRevoke, revoked], trivial, trivial, revoked⟩
    rw [← successor, Store.install_ledger]
    exact (Refresh.revocation_retains_lineage receipt).1

structure FinalInput where
  authorityId : String
  durable : Option Store
  read : ReplicaRead

def FinalInput.recovery (input : FinalInput) : RecoveryInput :=
  ⟨input.authorityId, input.durable, input.read.replica⟩

/-- Use reservations from disk and the actual request's current authority.
The caller's reserved list cannot undo committed replay protection. -/
def Store.readForFinal (store : Store) (read : ReplicaRead) : FinalRead :=
  ⟨{ read with authority := { read.authority with reserved := store.reserved } }, some store.checkpoint⟩

def finalize (input : FinalInput) : Option Store := do
  let store ← recover input.recovery
  let authority ← check (store.readForFinal input.read)
  return { store with reserved := authority.reserved }

def finalContract : Contract Unit FinalInput Store where
  input := ⟨"durable-OAuth-frontier-and-actual-effect", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"durably-reserved-OAuth-effect", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => finalize input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareFinal (input : FinalInput) : Except String (Store × Unit) :=
  match finalize input with
  | some store => .ok (store, ())
  | none => .error "Durable OAuth final use refused"

theorem final_retains_checkpoint_and_reservation
    (receipt : Invocation finalContract prepareFinal input) :
    ∃ store authority, recover input.recovery = some store ∧
      check (store.readForFinal input.read) = some authority ∧
      receipt.result.checkpoint = store.checkpoint ∧ receipt.result.reserved = authority.reserved := by
  have accepted := receipt.logic
  change finalize input = some receipt.result at accepted
  cases restored : recover input.recovery with
  | none => simp [finalize, restored] at accepted
  | some store =>
    cases checked : check (store.readForFinal input.read) with
    | none => simp [finalize, restored, checked] at accepted
    | some authority =>
      simp [finalize, restored, checked] at accepted
      rw [← accepted]
      exact ⟨store, authority, rfl, checked, rfl, rfl⟩

theorem cannot_finalize_from_failed_recovery (input : FinalInput)
    (refused : recover input.recovery = none) : finalize input = none := by
  simp [finalize, refused]

theorem durable_revocation_blocks_final (present : input.durable = some store)
    (linked : store.checkpoint.ledger.accessEntry input.read.attempt.grant.tokenHash = some entry)
    (revoked : entry.family ∈ store.checkpoint.ledger.revoked) : finalize input = none := by
  cases restored : recover input.recovery with
  | none => exact cannot_finalize_from_failed_recovery input restored
  | some actual =>
    have ⟨source, replica, _⟩ := recovery_retains_independent_store restored
    have same : actual = store := Option.some.inj (source.symm.trans present)
    subst actual
    have replica : input.read.replica = store.checkpoint := replica
    simp [finalize, restored, Store.readForFinal, check, replica,
      Refresh.revoked_access_refused _ linked revoked]

theorem persisted_revoke_refuses_final {before after : Store}
    (applied : before.revoke verified = some after)
    (present : input.durable = some after)
    (linked : after.checkpoint.ledger.accessEntry input.read.attempt.grant.tokenHash = some entry)
    (family : entry.family = (Refresh.RevocationInput.key ⟨before.checkpoint.ledger, verified⟩)) :
    finalize input = none :=
  durable_revocation_blocks_final present linked (family.symm ▸ persisted_revocation_marks_family applied)

theorem durable_reservation_blocks_final (present : input.durable = some store)
    (proof : input.read.attempt.proofKey = some key)
    (reserved : key ∈ store.reserved) : finalize input = none := by
  cases restored : recover input.recovery with
  | none => exact cannot_finalize_from_failed_recovery input restored
  | some actual =>
    have ⟨source, replica, _⟩ := recovery_retains_independent_store restored
    have same : actual = store := Option.some.inj (source.symm.trans present)
    subst actual
    have replica : input.read.replica = store.checkpoint := replica
    have refused := reserved_proof_refused { input.read.authority with reserved := store.reserved }
      input.read.attempt key proof reserved
    have access : Refresh.useAccess store.checkpoint.ledger
        { input.read.authority with reserved := store.reserved } input.read.attempt = none := by
      cases found : store.checkpoint.ledger.accessEntry input.read.attempt.grant.tokenHash <;>
        simp [Refresh.useAccess, found, refused]
    simp [finalize, restored, Store.readForFinal, check, replica, access]

end CedarPooSpec.Gateway.OAuth.Revocation.Recovery
