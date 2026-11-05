import Tests.Gateway.SettledLatePlan

namespace Tests.Gateway.SettledLate
open CedarPooSpec.Gateway.OAuth

/-- Alternate pre-install crashes, then recover one durable binding across
repeated lost confirmations. Every recovered step uses the public Contract. -/
def alternating (image : ReceiptRecovery.Image) (delayed first : ReceiptRecovery.Input)
    (retry : Revocation.Crash.BeginInput) : Bool := Id.run do
  let operation := delayed.request.operation
  let .ok identified := ReceiptIdentity.contract.invoke ReceiptIdentity.prepare
    (delayed.authority, delayed.request) | return false
  have symbolOperation : delayed.request.receiptSymbol.operation = operation := by
    obtain ⟨source, _, matched, _⟩ := ReceiptIdentity.accepted_mapping identified
    simpa [ReceiptIdentity.Request.receiptSymbol, ReceiptIdentity.project, operation] using
      congrArg ReceiptIdentity.Identity.operation matched.1
  let observe := SettledLatePlan.observe image
  let mut observed := #[observe image delayed retry "ready" "both"]
  let mut tracked : { state : ReceiptRecovery.Image // ReceiptRecovery.Trace image state } :=
    ⟨image, .start image⟩
  for round in [:2] do
    let before := tracked
    let item := { delayed with image := before.1, writer := before.1.oauth.writer }
    let .ok eligible := ReceiptRecovery.contract.invoke ReceiptRecovery.prepare
      { item with mode := .settled } | return false
    let _wouldBind := ReceiptRecovery.persistence_records eligible
    let input : ReceiptBatch.RecoveryInput := ⟨before.1, item, .staged⟩
    let .ok staged := ReceiptBatch.recoveryContract.invoke ReceiptBatch.prepareRecovery input
      | return false
    let _notInstalled := ReceiptBatch.recovery_staged_is_before staged rfl
    if staged.result != before.1 then return false
    let role := if round = 0 then "a" else "b"
    let peer := if round = 0 then "b" else "a"
    observed := observed.push (observe staged.result delayed retry "staged-crash" role)
    let step := ReceiptRecovery.Trace.trans before.2 (ReceiptBatch.recovery_trace staged)
    match advanced : Revocation.Crash.handoff staged.result.oauth staged.result.oauth.writer with
    | none => return false
    | some active =>
      let next : ReceiptRecovery.Image := { staged.result with oauth := active }
      observed := observed.push (observe next delayed retry "handoff" "authority")
      let oldWriter := ReceiptBatch.State.step { image := next } item
      let oldReplica := { item with
        image := next, writer := active.writer
        recovery := { item.recovery with placement := "retired-replica" } }
      let replicaStop := ReceiptBatch.State.step { image := next } oldReplica
      if oldWriter.stopped != some operation || oldWriter.image != next ||
          replicaStop.stopped != some operation || replicaStop.image != next then return false
      if (ReceiptRecovery.lookup next.rows operation).isSome then return false
      observed := observed.push (observe next delayed retry "fenced" peer)
      tracked := ⟨next, .authorization step (.handoff (.start staged.result.oauth) advanced)⟩
  let item := { delayed with image := tracked.1, writer := tracked.1.oauth.writer }
  let input : ReceiptBatch.RecoveryInput := ⟨tracked.1, item, .durable⟩
  let .ok installed := ReceiptBatch.recoveryContract.invoke ReceiptBatch.prepareRecovery input
    | return false
  let historyPrefix := ReceiptRecovery.Trace.trans tracked.2 (ReceiptBatch.recovery_trace installed)
  let row := ReceiptRecovery.Request.stored delayed.request
  if bound : ReceiptRecovery.lookup installed.result.rows operation = some row then
    observed := observed.push (observe installed.result delayed retry "durable-crash" "a")
    observed := observed.push (observe installed.result delayed retry "confirmed" "b")
    let mut resumed : { state : ReceiptRecovery.Image //
        ReceiptRecovery.Trace installed.result state } := ⟨installed.result, .start installed.result⟩
    for round in [:4] do
      let before := resumed
      match advanced : Revocation.Crash.handoff before.1.oauth before.1.oauth.writer with
      | none => return false
      | some active =>
        let next : ReceiptRecovery.Image := { before.1 with oauth := active }
        observed := observed.push (observe next delayed retry "handoff" "authority")
        let handoff : ReceiptRecovery.Trace installed.result next :=
          .authorization before.2 (.handoff (.start before.1.oauth) advanced)
        let original := { delayed with image := next, writer := active.writer }
        let duplicate : ReceiptBatch.RecoveryInput := ⟨next, original, .durable⟩
        let .ok confirmed := ReceiptBatch.recoveryContract.invoke ReceiptBatch.prepareRecovery duplicate
          | return false
        let role := if round % 2 = 0 then "a" else "b"
        let peerRole := if round % 2 = 0 then "b" else "a"
        observed := observed.push (observe confirmed.result delayed retry "confirmation-lost" role)
        let prior := { first with image := confirmed.result, writer := active.writer }
        let conflicting := { original with request := { original.request with outcomeSource :=
          { original.request.outcomeSource with signature := [99] } } }
        let .ok peer := ReceiptBatch.contract.invoke ReceiptBatch.prepare
          ⟨confirmed.result, [prior, conflicting, original, original]⟩ | return false
        if confirmed.result != next || peer.result.image != next ||
            peer.result.pending != [operation] then return false
        observed := observed.push (observe peer.result.image delayed retry "confirmed" peerRole)
        have folded : ReceiptRecovery.Trace confirmed.result peer.result.image := by
          have same := peer.logic
          change ReceiptBatch.Input.run _ = peer.result at same
          rw [← same]
          exact ReceiptBatch.fold_trace [prior, conflicting, original, original]
            { image := confirmed.result }
        resumed := ⟨peer.result.image, ReceiptRecovery.Trace.trans handoff
          (ReceiptRecovery.Trace.trans (ReceiptBatch.recovery_trace confirmed) folded)⟩
    let _immutable := ReceiptRecovery.trace_preserves_original resumed.2 bound
    let _identity := ReceiptRecovery.trace_preserves_receipt_identity resumed.2 bound
    let _sources := ReceiptRecovery.trace_preserves_receipt_sources resumed.2 bound
    let symbol := delayed.request.receiptSymbol
    have symbolicBound : ReceiptRecovery.lookup installed.result.rows symbol.operation = some row := by
      change ReceiptRecovery.lookup installed.result.rows delayed.request.receiptSymbol.operation = some row
      rw [symbolOperation]
      exact bound
    let _realized := ReceiptRecovery.trace_preserves_realization resumed.2 symbolicBound
    let _restored := ReceiptRecovery.trace_preserves_restoration
      (authority := delayed.authority) (request := delayed.request) resumed.2 symbolicBound
    let complete := ReceiptRecovery.Trace.trans historyPrefix resumed.2
    let finalRetry := { retry with
      image := resumed.1.oauth, operation := operation
      intent := delayed.request.symbolic.receipt.commit
      writer := resumed.1.oauth.writer, checkedWriter := resumed.1.oauth.writer }
    if burned : (image.oauth.retained.any fun entry => entry.intent.operation == finalRetry.operation) = true then
      let _noResend := ReceiptRecovery.trace_cannot_resend complete finalRetry burned
      observed := observed.push (observe resumed.1 delayed retry "recovered" "a")
      return decide (observed.toList = SettledLatePlan.steps) &&
        decide (ReceiptRecovery.lookup resumed.1.rows operation = some row) &&
        (Revocation.Crash.begin finalRetry).isNone
    else return false
  else return false

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
  return alternating image delayed first retry && decide (a.result.confirmed = [operation, operation, prior.request.operation]) &&
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

#print axioms CedarPooSpec.Gateway.OAuth.ReceiptRecovery.trace_cannot_resend
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptBatch.recovery_trace
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptBatch.recovery_staged_is_before
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptBatch.recovery_keeps_original
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptBatch.recovery_durable_binds

#print axioms CedarPooSpec.Gateway.OAuth.ReceiptBatch.recovery_keeps_authorization
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptBatch.recovery_refused_is_before
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptBatch.recovery_fenced_is_before

#print axioms CedarPooSpec.Gateway.OAuth.ReceiptRecovery.trace_preserves_receipt_identity
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptRecovery.trace_preserves_receipt_sources

#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.realized_symbol_and_sources
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.realized_source_digests
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.realization_wrong_operation
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.realization_foreign_receiver
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.realization_foreign_provider
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.realization_foreign_witness
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.realization_wrong_receipt
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.realization_check_exact
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptRecovery.trace_preserves_realization

#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.restoration_requires_sources
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.restoration_rejects_substitution
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.restoration_missing_refused
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptIdentity.restoration_idempotent
#print axioms CedarPooSpec.Gateway.OAuth.ReceiptRecovery.trace_preserves_restoration
