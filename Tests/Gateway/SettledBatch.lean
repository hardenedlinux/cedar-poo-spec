import CedarPooSpec.Gateway.OAuthReceiptBatch
import Tests.Gateway.SettledLate

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
  let some pin := original.recovery.independent | return false
  -- Build the historical receiver checkpoint before the migration starts.
  -- During the batch the original signed receipt is withheld, not executed again.
  let dispatch : CedarPooSpec.Admission.DispatchBinding :=
    ⟨⟨absent⟩, "historical-intent-digest", pin.image.cut⟩
  let delivery : Receiver.Delivery := ⟨dispatch, "original-channel", unknown⟩
  let receiverInput : Receiver.Input :=
    ⟨pin.image, delivery, dispatch, delivery.channel, retained.intent, true⟩
  let .ok recorded := Receiver.contract.invoke Receiver.prepare receiverInput | return false
  let checkpoint := { pin with image := recorded.result }
  let refresh := fun recovery => { recovery with
    independent := some checkpoint, placement := checkpoint.active, replica := checkpoint.image
    : Receiver.ManagedReconciliation }
  let original := { original with recovery := refresh original.recovery }
  let missing := refresh missing
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
  let source : ReceiptIdentity.CanonicalReceipt :=
    { symbolic := unknown, intent := retained.intent
      intentSource := ⟨retained.intent.payload, retained.intent.signature⟩
      outcomeSource := ⟨[5], unknown.signature⟩ }
  let reader (op : String) : Option ReceiptIdentity.CanonicalReceipt :=
    if op = absent then some source else original.authority.read op
  let authority := { original.authority with read := reader }
  let request : ReceiptIdentity.Request :=
    { operation := absent, symbolic := unknown
      identity := ReceiptIdentity.project authority absent source
      intentSource := source.intentSource, outcomeSource := source.outcomeSource }
  let late := { original with
    authority, request
    recovery := { original.recovery with audit := { original.recovery.audit with
      operation := absent, actions := [unknown.receipt.action], outcomes := [unknown] } } }
  let lateSafe := Tests.Gateway.SettledLate.exercise again.result.image late (update first) retry
  return lateSafe && decide (a.result.confirmed = [operation]) &&
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
