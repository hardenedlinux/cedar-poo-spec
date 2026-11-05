import CedarPooSpec.Gateway.OAuthReceiptBatch

namespace Tests.Gateway.SettledLate
open CedarPooSpec.Gateway.OAuth

def exercise (image : ReceiptRecovery.Image) (delayed first : ReceiptRecovery.Input)
    (retry : Revocation.Crash.BeginInput) : Bool := Id.run do
  let operation := delayed.request.operation
  if (ReceiptRecovery.lookup image.rows operation).isSome then return false
  let some one := Revocation.Crash.handoff image.oauth image.oauth.writer | return false
  let some two := Revocation.Crash.handoff one one.writer | return false
  let pending := { image with oauth := two }
  let ready := fun item => { item with image := pending, writer := two.writer : ReceiptRecovery.Input }
  let original := ready delayed
  let prior := ready first
  let conflict := { original with request := { original.request with outcomeSource :=
    { original.request.outcomeSource with signature := [99] } } }
  let .ok a := ReceiptBatch.contract.invoke ReceiptBatch.prepare
    ⟨pending, [conflict, original, original, prior]⟩ | return false
  let .ok b := ReceiptBatch.contract.invoke ReceiptBatch.prepare
    ⟨a.result.image, [prior, original, conflict, original]⟩ | return false
  let .ok alternate := ReceiptBatch.contract.invoke ReceiptBatch.prepare
    ⟨pending, [prior, original, conflict, original]⟩ | return false
  let .ok single := ReceiptRecovery.contract.invoke ReceiptRecovery.prepare original | return false
  let durable := Revocation.Crash.recoverImage .durable pending a.result.image
  let staged := Revocation.Crash.recoverImage .staged pending a.result.image
  if same : durable.rows = single.result.rows then
    have bound : ReceiptRecovery.lookup a.result.image.rows original.request.identity.operation =
        some (ReceiptRecovery.Request.stored original.request) := by
      change ReceiptRecovery.lookup durable.rows original.request.identity.operation = _
      rw [same]
      exact ReceiptRecovery.persistence_records single
    let _kept := ReceiptBatch.batch_keeps_original b bound
    pure ()
  else return false
  let mut tracked : { state : ReceiptRecovery.Image // ReceiptRecovery.Trace durable state } :=
    ⟨durable, .start durable⟩
  for _ in [:3] do
    let before := tracked
    match applied : Revocation.Crash.handoff before.1.oauth before.1.oauth.writer with
    | none => return false
    | some active =>
      let next : ReceiptRecovery.Image := { before.1 with oauth := active }
      let history : ReceiptRecovery.Trace durable next :=
        .authorization before.2 (.handoff (.start before.1.oauth) applied)
      let update := fun item => { item with image := next, writer := active.writer : ReceiptRecovery.Input }
      let input : ReceiptBatch.Input := ⟨next, [update original, update conflict, update prior, update original]⟩
      let .ok confirmation := ReceiptBatch.contract.invoke ReceiptBatch.prepare input | return false
      if confirmation.result.image != next then return false
      tracked := ⟨confirmation.result.image,
        ReceiptRecovery.Trace.trans history (by
          have equal := confirmation.logic
          change input.run = confirmation.result at equal
          rw [← equal]
          exact ReceiptBatch.fold_trace input.items { image := input.image })⟩
  return decide (a.result.confirmed = [operation, operation, prior.request.operation]) &&
    decide (a.result.pending = [operation]) &&
    decide (b.result.confirmed = [prior.request.operation, operation, operation]) &&
    decide (b.result.pending = [operation]) &&
    decide (b.result.image = a.result.image) &&
    decide (alternate.result.image = a.result.image) &&
    (ReceiptRecovery.lookup staged.rows operation).isNone &&
    decide (ReceiptRecovery.lookup tracked.1.rows operation =
      some (ReceiptRecovery.Request.stored original.request)) &&
    (Revocation.Crash.begin { retry with
      image := tracked.1.oauth
      operation := operation
      intent := original.request.symbolic.receipt.commit
      writer := tracked.1.oauth.writer
      checkedWriter := tracked.1.oauth.writer }).isNone

end Tests.Gateway.SettledLate
