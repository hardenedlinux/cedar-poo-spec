import CedarPooSpec.Gateway.OAuthReceiptBatch

namespace Tests.Gateway.SettledBatch
open CedarPooSpec.Gateway.OAuth

def exercise (original : ReceiptRecovery.Input) (missing : Receiver.ManagedReconciliation)
    (verified : PAR.VerifiedClient Refresh.RefreshDigest) (retry : Revocation.Crash.BeginInput) : Bool := Id.run do
  let operation := original.request.operation
  let absent := missing.audit.operation
  let currentMissing := { missing.audit with image := original.image.oauth }
  let some retained := currentMissing.retained | return false
  let unknown := { original.request.symbolic with receipt :=
    { original.request.symbolic.receipt with
      commit := retained.intent
      action := { original.request.symbolic.receipt.action with operation := absent } } }
  let legacy := original.image.oauth
  let ledger := { legacy.oauth.checkpoint.ledger with revoked := [] }
  let active := { legacy with
    oauth := { legacy.oauth with checkpoint := { legacy.oauth.checkpoint with ledger } }
    resolved := unknown :: legacy.resolved }
  let image := { original.image with
    oauth := active
    legacyOutcomes := (absent, original.request.identity.outcomeDigest) :: original.image.legacyOutcomes }
  let first := { original with image }
  let noEvidence := { first with
    request := { first.request with
      operation := absent
      identity := { first.request.identity with operation := absent } }
    recovery := { missing with audit := { missing.audit with outcomes := [] } } }
  let conflicting := { first with request := { first.request with outcomeSource :=
    { first.request.outcomeSource with signature := [99] } } }
  let .ok a := ReceiptBatch.contract.invoke ReceiptBatch.prepare ⟨image, [first]⟩ | return false
  let .ok b := ReceiptBatch.contract.invoke ReceiptBatch.prepare ⟨a.result.image, [first]⟩ | return false
  let some handed := Revocation.Crash.handoff b.result.image.oauth b.result.image.oauth.writer | return false
  let some revoked := Revocation.Crash.revoke handed handed.writer verified | return false
  let some latest := Revocation.Crash.handoff revoked revoked.writer | return false
  let durable := { b.result.image with oauth := latest }
  let prefixA : ReceiptBatch.State := { a.result with image := durable }
  let prefixB : ReceiptBatch.State := { b.result with image := durable }
  let suffixA := [noEvidence, conflicting].foldl ReceiptBatch.State.step prefixA
  let suffixB := [conflicting, noEvidence].foldl ReceiptBatch.State.step prefixB
  let update := fun item => { item with image := durable, writer := latest.writer : ReceiptRecovery.Input }
  let .ok resumed := ReceiptBatch.contract.invoke ReceiptBatch.prepare
    ⟨durable, [update noEvidence, update first, update conflicting, update first]⟩ | return false
  let lost := Revocation.Crash.recoverImage .durable durable resumed.result.image
  let staged := Revocation.Crash.recoverImage .staged image a.result.image
  let .ok again := ReceiptBatch.contract.invoke ReceiptBatch.prepare
    ⟨lost, [update first, update conflicting, update noEvidence, update first]⟩ | return false
  let .ok single := ReceiptRecovery.contract.invoke ReceiptRecovery.prepare first | return false
  if aligned : lost.rows = single.result.rows then
    let _kept := ReceiptBatch.batch_keeps_original again
      (by simpa [aligned] using ReceiptRecovery.persistence_records single)
    pure ()
  else return false
  return decide (a.result.confirmed = [operation]) &&
    decide (b.result.image = a.result.image) &&
    decide (suffixA.stopped = some absent) &&
    decide (suffixB.stopped = some operation) &&
    decide (suffixA.image = durable) && decide (suffixB.image = durable) &&
    decide (suffixA.confirmed = [operation]) && decide (suffixB.confirmed = [operation]) &&
    decide (resumed.result.confirmed = [operation, operation]) &&
    decide (resumed.result.pending = [absent, operation]) &&
    decide (again.result.pending = [operation, absent]) &&
    decide (again.result.image = lost) && staged.rows.isEmpty &&
    (ReceiptRecovery.lookup again.result.image.rows absent).isNone &&
    (Revocation.Crash.begin { retry with
      image := again.result.image.oauth
      writer := latest.writer, checkedWriter := latest.writer }).isNone

end Tests.Gateway.SettledBatch
