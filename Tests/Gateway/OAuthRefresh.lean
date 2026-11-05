import CedarPooSpec.Gateway.OAuthReceiver

namespace Tests.Gateway.OAuthRefresh
open CedarPooSpec.Gateway.OAuth
open CedarPooSpec.Gateway.OAuth.Refresh

private def session : Code.Session :=
  ⟨"issuer", "client", "https://client.example/callback", "state", "browser",
    "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM"⟩
private def registration : PAR.Registration :=
  ⟨session.issuer, session.client, .privateKeyJwt "client-key", [session.redirect], ["patient.read"]⟩
private def verified (request : α) : PAR.VerifiedClient α :=
  ⟨registration.issuer, registration.client, registration.credential, request⟩
private def digest : RefreshDigest := ⟨"refresh-digest"⟩

private def tokenSender : Confirmation → PAR.TokenSender
  | .dpop key => .dpop ⟨key⟩
  | .mtls certificate => .mtls certificate

private def overlappingRecoveryExercise (takeover : Receiver.LegacyBatchInput)
    (settled prior : Receiver.LegacyBatchState)
    (original conflict missing : Receiver.ManagedReconciliation)
    (retry : Revocation.Crash.BeginInput) : Bool := Id.run do
  let some pin := original.independent | return false
  let some (_, outcome) := Receiver.evidence pin.image ⟨original.audit.operation⟩ | return false
  let operation := original.audit.operation
  let pendingOperation := missing.audit.operation
  let peerState := { prior with image := takeover.image }
  let retired := { original with audit := { original.audit with writer := prior.image.writer } }
  let stopped := [retired, missing].foldl
    (Receiver.LegacyBatchState.step takeover.trusted) peerState
  let recovered := Revocation.Crash.recoverImage .durable takeover.image settled.image
  let some writer := Revocation.Crash.handoff recovered recovered.writer | return false
  let promotion : Receiver.PromotionInput :=
    ⟨some pin, pin, pin.image, "after-lost-ack"⟩
  let .ok receiver := Receiver.promotionContract.invoke Receiver.preparePromotion promotion | return false
  let receipt := { original with
    independent := some receiver.result
    placement := "after-lost-ack"
    replica := receiver.result.image
    audit := { original.audit with writer := writer.writer } }
  let other := { receipt with audit := { conflict.audit with writer := writer.writer } }
  let missingReceipt := { receipt with audit := { missing.audit with writer := writer.writer } }
  let first : Receiver.LegacyBatchInput :=
    ⟨writer, takeover.trusted, [receipt, other, missingReceipt, receipt]⟩
  let .ok confirmed := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch first | return false
  let second : Receiver.LegacyBatchInput :=
    ⟨confirmed.result.image, takeover.trusted, [missingReceipt, receipt, receipt, other]⟩
  let .ok repeated := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch second | return false
  let .ok recoveryPrefix := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch
    { first with items := [receipt] } | return false
  let .ok peerPrefix := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch
    { first with items := [missingReceipt, receipt] } | return false
  let crashedAgain := Revocation.Crash.recoverImage .durable writer recoveryPrefix.result.image
  let some standby := Revocation.Crash.handoff crashedAgain writer.writer | return false
  let some active := Revocation.Crash.handoff standby standby.writer | return false
  let nextPromotion : Receiver.PromotionInput :=
    ⟨some receiver.result, receiver.result, receiver.result.image, "recovery-standby"⟩
  let .ok nextReceiver := Receiver.promotionContract.invoke Receiver.preparePromotion nextPromotion | return false
  let finalPromotion : Receiver.PromotionInput :=
    ⟨some nextReceiver.result, nextReceiver.result, nextReceiver.result.image, "recovery-active"⟩
  let .ok finalReceiver := Receiver.promotionContract.invoke Receiver.preparePromotion finalPromotion | return false
  let latest := { receipt with
    independent := some finalReceiver.result
    placement := "recovery-active"
    replica := finalReceiver.result.image
    audit := { receipt.audit with writer := active.writer } }
  let latestConflict := { latest with audit := { other.audit with writer := active.writer } }
  let latestMissing := { latest with audit := { missingReceipt.audit with writer := active.writer } }
  let fencedPeer := { peerPrefix.result with image := active }
  let peerSuffix := [receipt, other].foldl
    (Receiver.LegacyBatchState.step takeover.trusted) fencedPeer
  let finalInput : Receiver.LegacyBatchInput :=
    ⟨active, takeover.trusted, [latest, latestConflict, latestMissing, latest]⟩
  let .ok finalFirst := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch finalInput | return false
  let finalReordered := { finalInput with
    image := finalFirst.result.image
    items := [latestMissing, latest, latest, latestConflict] }
  let .ok finalSecond := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch finalReordered | return false
  let retryAfterRecovery := { retry with
    image := finalSecond.result.image
    writer := active.writer
    checkedWriter := active.writer }
  return decide (stopped = { peerState with stopped := some operation }) &&
    decide (confirmed.result.image = writer) &&
    decide (repeated.result.image = writer) &&
    decide (confirmed.result.confirmed = [operation, operation]) &&
    decide (repeated.result.confirmed = confirmed.result.confirmed) &&
    decide (confirmed.result.pending = [operation, pendingOperation]) &&
    decide (repeated.result.pending = [pendingOperation, operation]) &&
    decide (repeated.result.image.settledOutcome operation = some outcome) &&
    decide (Revocation.Crash.effectStatus repeated.result.image pendingOperation = .unresolved) &&
    decide (recoveryPrefix.result.image = writer) &&
    decide (peerPrefix.result.image = writer) &&
    decide (peerPrefix.result.confirmed = [operation]) &&
    decide (peerPrefix.result.pending = [pendingOperation]) &&
    decide (peerSuffix = { fencedPeer with stopped := some operation }) &&
    decide (finalFirst.result.image = active) &&
    decide (finalSecond.result.image = active) &&
    decide (finalFirst.result.confirmed = [operation, operation]) &&
    decide (finalSecond.result.confirmed = finalFirst.result.confirmed) &&
    decide (finalSecond.result.pending = [pendingOperation, operation]) &&
    decide (finalSecond.result.image.settledOutcome operation = some outcome) &&
    decide (finalSecond.result.image.retained = writer.retained) &&
    decide (finalSecond.result.image.oauth = writer.oauth) &&
    decide (Revocation.Crash.effectStatus finalSecond.result.image pendingOperation = .unresolved) &&
    (Revocation.Crash.begin retryAfterRecovery).isNone

private def crashExercise (durable : Revocation.Recovery.Store)
    (read : Revocation.ReplicaRead) : Bool := Id.run do
  let openRevocation : Revocation.Crash.Image := { oauth := durable }
  let intent : CedarPooSpec.Gateway.EffectProtocol.CommitRef := ⟨"effect", [1], [2]⟩
  let history : Revocation.Crash.History :=
    ⟨"log", [intent], true, some (CedarPooSpec.Gateway.Lifecycle.WitnessFrontier.observe "log" [intent])⟩
  let begin : Revocation.Crash.BeginInput :=
    ⟨openRevocation, 0, 0, read, intent.operation, intent, "provider", history, none⟩
  let .ok started := Revocation.Crash.beginContract.invoke Revocation.Crash.prepareBegin begin | return false
  let some handed := Revocation.Crash.handoff started.result 0 | return false
  let some revoked := Revocation.Crash.revoke handed 1 (verified digest) | return false
  let stale := Revocation.Crash.recoverImage .staged handed revoked
  let live := Revocation.Crash.recoverImage .durable handed revoked
  let source : CedarPooSpec.ZeroTrust.FactAuthority String String :=
    ⟨fun field => ⟨"issuer", "subject", "fhir", "source", field, "value", 0, .observed, 0, 20⟩, fun _ => true, 14⟩
  let trust : CedarPooSpec.Gateway.EffectProtocol.ProviderAuditTrust :=
    ⟨"provider", "log", fun _ outcome => outcome.signature == [7], fun _ _ _ => true⟩
  let action : CedarPooSpec.Gateway.EffectProtocol.AuditRecord := ⟨intent.operation, "result"⟩
  let outcome : CedarPooSpec.Gateway.EffectProtocol.ProviderOutcome :=
    ⟨{}, "cedar-poo/provider-outcome", "log", ⟨action, intent⟩, [7]⟩
  let cut : CedarPooSpec.Admission.ReceiverCut := ⟨"receiver", 0⟩
  let receiver : Receiver.Image := { cut := cut }
  let dispatch : CedarPooSpec.Admission.DispatchBinding := ⟨⟨intent.operation⟩, "effect-digest", cut⟩
  let delivery : Receiver.Delivery := ⟨dispatch, "channel-one", outcome⟩
  let request : Receiver.Input := ⟨receiver, delivery, dispatch, "channel-one", intent, true⟩
  let .ok delivered := Receiver.contract.invoke Receiver.prepare request | return false
  let authority := openRevocation.oauth.checkpoint.authorityId
  let primary : Receiver.Checkpoint := ⟨"primary", receiver, none, some authority, "receiver-pin"⟩
  let managedBegin := { begin with receiver := some primary.binding }
  let .ok managedStart := Revocation.Crash.beginContract.invoke Revocation.Crash.prepareBegin managedBegin | return false
  let managed : Receiver.ManagedInput := ⟨some primary, "primary", request, managedBegin⟩
  let .ok committed := Receiver.managedContract.invoke Receiver.prepareManaged managed | return false
  let reservedOnly := Receiver.recoverReservation started primary
  let firstTakeover : Receiver.PromotionInput :=
    ⟨some reservedOnly.receiver, reservedOnly.receiver, reservedOnly.receiver.image, "standby"⟩
  let .ok first := Receiver.promotionContract.invoke Receiver.preparePromotion firstTakeover | return false
  let secondTakeover : Receiver.PromotionInput :=
    ⟨some first.result, first.result, first.result.image, "successor"⟩
  let .ok second := Receiver.promotionContract.invoke Receiver.preparePromotion secondTakeover | return false
  let some nextWriter := Revocation.Crash.handoff reservedOnly.oauth 0 | return false
  let some finalWriter := Revocation.Crash.handoff nextWriter 1 | return false
  let .ok unknown := Revocation.Crash.statusContract.invoke Revocation.Crash.prepareStatus
    ⟨finalWriter, 2, intent.operation⟩ | return false
  let some revokedWriter := Revocation.Crash.revoke finalWriter 2 (verified digest) | return false
  let .ok unknownAfterRevoke := Revocation.Crash.statusContract.invoke Revocation.Crash.prepareStatus
    ⟨revokedWriter, 2, intent.operation⟩ | return false
  let changedIntent : CedarPooSpec.Gateway.EffectProtocol.CommitRef := ⟨intent.operation, [3], [4]⟩
  let reviewed : Revocation.Crash.History :=
    ⟨"log", [changedIntent], true,
      some (CedarPooSpec.Gateway.Lifecycle.WitnessFrontier.observe "log" [changedIntent])⟩
  let retryAuthorization : Revocation.Crash.BeginInput :=
    ⟨finalWriter, 2, 2, read, intent.operation, changedIntent, "provider", reviewed, none⟩
  let newCut := { dispatch with cut := second.result.image.cut }
  let changedOutcome := { outcome with receipt := ⟨action, changedIntent⟩ }
  let retryDelivery : Receiver.Input :=
    ⟨second.result.image, ⟨newCut, "other-channel", changedOutcome⟩,
      newCut, "other-channel", changedIntent, true⟩
  let unknownRetry : Receiver.ManagedInput := ⟨some second.result, "successor", retryDelivery, retryAuthorization⟩
  let unknownReconcile : Revocation.Crash.ReconcileInput :=
    ⟨finalWriter, 2, intent.operation, trust, source, history, [], []⟩
  let some advanced := Receiver.advance delivered.result cut | return false
  let restored := Revocation.Crash.recoverImage .durable delivered.result advanced
  let staged := Revocation.Crash.recoverImage .staged receiver delivered.result
  let pin : Receiver.Checkpoint := { primary with image := restored }
  let promotion : Receiver.PromotionInput := ⟨some pin, pin, restored, "standby"⟩
  let .ok promoted := Receiver.promotionContract.invoke Receiver.preparePromotion promotion | return false
  let stagedPromotion := Revocation.Crash.recoverImage .staged pin promoted.result
  let committedPromotion := Revocation.Crash.recoverImage .durable pin promoted.result
  let fork : Receiver.Image := { restored with delivered := [] }
  let contender : Receiver.PromotionInput := ⟨some committedPromotion, pin,
    committedPromotion.image, "loser"⟩
  let recovery : Receiver.PromotionRecovery :=
    ⟨some committedPromotion, pin, "standby", committedPromotion.image⟩
  let .ok recovered := Receiver.promotionRecoveryContract.invoke
    Receiver.preparePromotionRecovery recovery | return false
  let next : Receiver.PromotionInput :=
    ⟨some committedPromotion, committedPromotion, committedPromotion.image, "successor"⟩
  let .ok successor := Receiver.promotionContract.invoke Receiver.preparePromotion next | return false
  let some (action, outcome) := Receiver.evidence successor.result.image dispatch.operation | return false
  let newDispatch := { dispatch with cut := successor.result.image.cut }
  let retry : Receiver.Input := ⟨successor.result.image, ⟨newDispatch, "channel-two", outcome⟩,
    newDispatch, "channel-two", intent, true⟩
  let reconcile : Revocation.Crash.ReconcileInput := ⟨live, 1, intent.operation, trust, source, history, [action], [outcome]⟩
  let .ok settled := Revocation.Crash.reconcileContract.invoke Revocation.Crash.prepareReconcile reconcile | return false
  let unrelated : CedarPooSpec.Gateway.EffectProtocol.CommitRef := ⟨"later-effect", [9], [10]⟩
  let extendedEntries := history.entries ++ [unrelated]
  let extended : Revocation.Crash.History :=
    ⟨"log", extendedEntries, true,
      some (CedarPooSpec.Gateway.Lifecycle.WitnessFrontier.observe "log" extendedEntries)⟩
  let late : Revocation.Crash.ReconcileInput :=
    ⟨revokedWriter, 2, intent.operation, trust, source, extended, [action], [outcome]⟩
  let .ok lateSettlement := Revocation.Crash.reconcileContract.invoke Revocation.Crash.prepareReconcile late
    | return false
  let differentAction := { action with value := "different" }
  let conflicting := { outcome with receipt := ⟨differentAction, intent⟩ }
  let conflictingEvidence : Revocation.Crash.ReconcileInput :=
    ⟨lateSettlement.result, 2, intent.operation, trust, source, extended, [differentAction], [conflicting]⟩
  let .ok beforeRevoke := Revocation.Crash.reconcileContract.invoke Revocation.Crash.prepareReconcile
    { late with image := finalWriter } | return false
  let durableWithoutAck := Revocation.Crash.recoverImage .durable finalWriter beforeRevoke.result
  let some postStandby := Revocation.Crash.handoff durableWithoutAck 2 | return false
  let some postRevoked := Revocation.Crash.revoke postStandby 3 (verified digest) | return false
  let some postActive := Revocation.Crash.handoff postRevoked 3 | return false
  let confirmed : Revocation.Crash.ReconcileInput := { late with image := postActive, writer := 4 }
  let some managedStandby := Revocation.Crash.handoff committed.result.oauth 0 | return false
  let some managedRevoked := Revocation.Crash.revoke managedStandby 1 (verified digest) | return false
  let some managedActive := Revocation.Crash.handoff managedRevoked 1 | return false
  let managedAudit := { late with image := managedActive }
  let anchored : Receiver.ManagedReconciliation :=
    ⟨some successor.result, "successor", successor.result.image, managedAudit⟩
  let conflictAudit := { managedAudit with actions := [differentAction], outcomes := [conflicting] }
  let .ok anchoredSettlement := Receiver.managedReconciliationContract.invoke
    Receiver.prepareManagedReconciliation anchored | return false
  let legacyEntries := managedActive.retained.map
    (fun entry => { entry with receiver := none, legacy := true })
  let legacyImage := { managedActive with retained := legacyEntries }
  let legacyAudit := { managedAudit with image := legacyImage }
  let legacyRecovery := { anchored with audit := legacyAudit }
  let migration : Receiver.LegacyMigration := ⟨legacyRecovery, successor.result.binding⟩
  let .ok migrated := Receiver.legacyMigrationContract.invoke Receiver.prepareLegacyMigration migration | return false
  let missingEntry : Revocation.Crash.Retained :=
    ⟨unrelated, CedarPooSpec.Gateway.Lifecycle.WitnessFrontier.observe "log" extendedEntries,
      "provider", none, true⟩
  let batchImage := { legacyImage with retained := missingEntry :: legacyImage.retained }
  let missingAudit := { legacyAudit with operation := unrelated.operation, actions := [], outcomes := [] }
  let missingItem := { legacyRecovery with audit := missingAudit }
  let batchInput : Receiver.LegacyBatchInput :=
    ⟨batchImage, successor.result.binding, [missingItem, legacyRecovery]⟩
  let .ok batch := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch batchInput | return false
  let withheldAudit := { legacyAudit with actions := [], outcomes := [] }
  let withheldItem := { legacyRecovery with audit := withheldAudit }
  let lateStart := { batchImage with oauth := managedStandby.oauth }
  let withholding : Receiver.LegacyBatchInput :=
    { batchInput with image := lateStart, items := [withheldItem, missingItem] }
  let .ok pending := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch withholding | return false
  let reopenedImage := Revocation.Crash.recoverImage .durable lateStart pending.result.image
  let some restartedWriter := Revocation.Crash.handoff reopenedImage 2 | return false
  let restartPromotion : Receiver.PromotionInput :=
    ⟨some successor.result, successor.result, successor.result.image, "restart"⟩
  let .ok restart := Receiver.promotionContract.invoke Receiver.preparePromotion restartPromotion | return false
  let lateAudit := { legacyAudit with writer := 3 }
  let lateItem : Receiver.ManagedReconciliation :=
    ⟨some restart.result, "restart", restart.result.image, lateAudit⟩
  let lateConflict := { lateItem with audit := { lateAudit with actions := [differentAction], outcomes := [conflicting] } }
  let resumedLate : Receiver.LegacyBatchInput :=
    ⟨restartedWriter, successor.result.binding, [lateConflict, lateItem]⟩
  let .ok lateBatch := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch resumedLate | return false
  let stagedLate := Revocation.Crash.recoverImage .staged restartedWriter lateBatch.result.image
  let some afterStaged := Revocation.Crash.handoff stagedLate 3 | return false
  let stagedLatePromotion : Receiver.PromotionInput :=
    ⟨some restart.result, restart.result, restart.result.image, "after-staged"⟩
  let .ok stagedSuccessor := Receiver.promotionContract.invoke Receiver.preparePromotion stagedLatePromotion | return false
  let recoveredOriginal := { lateItem with
    independent := some stagedSuccessor.result
    placement := "after-staged"
    replica := stagedSuccessor.result.image
    audit := { lateAudit with writer := 4 } }
  let recoveredWithheld := { recoveredOriginal with audit := { withheldAudit with writer := 4 } }
  let recoveredConflict := { recoveredOriginal with audit := { lateConflict.audit with writer := 4 } }
  let afterStagedInput : Receiver.LegacyBatchInput :=
    ⟨afterStaged, successor.result.binding, [recoveredConflict, recoveredWithheld]⟩
  let .ok afterStagedBatch := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch afterStagedInput | return false
  let retiredWriter := { recoveredOriginal with audit := lateAudit }
  let retiredReplica := { recoveredOriginal with placement := "restart", replica := restart.result.image }
  let retiredWriterBatch : Receiver.LegacyBatchInput := { afterStagedInput with items := [retiredWriter] }
  let retiredReplicaBatch : Receiver.LegacyBatchInput := { afterStagedInput with items := [retiredReplica] }
  let retiredWriterRun : Receiver.LegacyBatchState := retiredWriterBatch.run
  let retiredReplicaRun : Receiver.LegacyBatchState := retiredReplicaBatch.run
  let .ok commitAgain := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch
    { afterStagedInput with items := [recoveredOriginal] } | return false
  let lateDurable := Revocation.Crash.recoverImage .durable afterStaged commitAgain.result.image
  let some lateWriter := Revocation.Crash.handoff lateDurable 4 | return false
  let some lateRevoked := Revocation.Crash.revoke lateWriter 5 (verified digest) | return false
  let some revokedFirst := Revocation.Crash.revoke lateDurable 4 (verified digest) | return false
  let some revokedThenHandedOff := Revocation.Crash.handoff revokedFirst 4 | return false
  let some finalLateWriter := Revocation.Crash.handoff lateRevoked 5 | return false
  let nextLatePromotion : Receiver.PromotionInput :=
    ⟨some stagedSuccessor.result, stagedSuccessor.result, stagedSuccessor.result.image, "next-late"⟩
  let .ok nextLate := Receiver.promotionContract.invoke Receiver.preparePromotion nextLatePromotion | return false
  let finalLatePromotion : Receiver.PromotionInput :=
    ⟨some nextLate.result, nextLate.result, nextLate.result.image, "resumed"⟩
  let .ok finalLate := Receiver.promotionContract.invoke Receiver.preparePromotion finalLatePromotion | return false
  let lateOriginal := { lateItem with
    independent := some finalLate.result
    placement := "resumed"
    replica := finalLate.result.image
    audit := { lateAudit with writer := 6 } }
  let lateOther := { lateOriginal with audit := { lateConflict.audit with writer := 6 } }
  let lateMissing := { lateOriginal with audit := { missingAudit with writer := 6 } }
  let some takeoverRevoked := Revocation.Crash.revoke afterStaged 4 (verified digest) | return false
  let some takeoverSuccessor := Revocation.Crash.handoff takeoverRevoked 4 | return false
  let some takeoverFinal := Revocation.Crash.handoff takeoverSuccessor 5 | return false
  let takeoverInput : Receiver.LegacyBatchInput :=
    ⟨takeoverFinal, successor.result.binding, [lateOther, lateMissing]⟩
  let .ok takeoverPending := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch takeoverInput | return false
  let .ok takeoverRecovered := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch
    { takeoverInput with items := [lateOriginal, lateOriginal] } | return false
  let committedPrefix : Receiver.LegacyBatchState :=
    { commitAgain.result with image := finalLateWriter }
  let staleSuffix := { lateMissing with audit := { missingAudit with writer := 4 } }
  let stoppedSuffix := [staleSuffix, lateOriginal].foldl
    (Receiver.LegacyBatchState.step successor.result.binding) committedPrefix
  let lateRetry : Receiver.LegacyBatchInput :=
    ⟨finalLateWriter, successor.result.binding, [lateOriginal, lateOther, lateMissing, lateOriginal]⟩
  let .ok lateRetried := Receiver.legacyBatchContract.invoke Receiver.prepareLegacyBatch lateRetry | return false
  let staleLate := { lateItem with replica := successor.result.image }
  let staleLateBatch : Receiver.LegacyBatchInput := { resumedLate with items := [staleLate] }
  let fencedMissing := { missingItem with placement := "standby" }
  let staleReplicaBatch : Receiver.LegacyBatchInput := { batchInput with items := [fencedMissing, legacyRecovery] }
  let staleRun : Receiver.LegacyBatchState := staleReplicaBatch.run
  let rerunBatch := { batchInput with image := batch.result.image }
  let oldWriterAudit := { legacyAudit with writer := 1 }
  let oldWriterRecovery := { legacyRecovery with audit := oldWriterAudit }
  let oldReplicaRecovery := { legacyRecovery with placement := "standby" }
  let migratedAudit := { legacyAudit with image := migrated.result }
  let migratedRecovery := { anchored with audit := migratedAudit }
  let legacyConflictAudit := { legacyAudit with actions := [differentAction], outcomes := [conflicting] }
  let legacyConflict := { legacyRecovery with audit := legacyConflictAudit }
  let missingCommit := { legacyRecovery with independent := some second.result, replica := second.result.image }
  let migratedRetry := { retryAuthorization with image := migrated.result, writer := 2, checkedWriter := 2 }
  let foreignPin := { successor.result with receiverAuthority := "foreign-pin" }
  let foreignLegacy := { legacyRecovery with independent := some foreignPin }
  let anchoredRetry := { managedAudit with image := anchoredSettlement.result }
  let revokedUse := { begin with image := live, writer := 1, checkedWriter := 1 }
  let afterTakeover : Receiver.ManagedInput :=
    ⟨some successor.result, "successor", retry, revokedUse⟩
  return decide (unknown.result = Revocation.Crash.EffectStatus.unresolved) &&
    decide (unknownAfterRevoke.result = unknown.result) &&
    !(Revocation.Crash.prepareStatus ⟨finalWriter, 0, intent.operation⟩).isOk &&
    (Receiver.evidence second.result.image dispatch.operation).isNone &&
    (Revocation.Crash.reconcile unknownReconcile).isNone &&
    (Revocation.Crash.reconcile { late with actions := [] }).isNone &&
    (Revocation.Crash.reconcile { late with outcomes := [outcome, conflicting] }).isNone &&
    decide (lateSettlement.result.oauth = revokedWriter.oauth) &&
    decide (Revocation.Crash.effectStatus lateSettlement.result intent.operation = .reconciled) &&
    decide (lateSettlement.result.settledOutcome intent.operation = some outcome) &&
    decide (Revocation.Crash.reconcile { late with image := lateSettlement.result } = some lateSettlement.result) &&
    (Revocation.Crash.reconcile conflictingEvidence).isNone &&
    decide (pending.result.image = lateStart) &&
    decide (pending.result.pending = [intent.operation, unrelated.operation]) &&
    decide (lateBatch.result.confirmed = [intent.operation]) &&
    decide (lateBatch.result.pending = [intent.operation]) &&
    decide (lateBatch.result.image.settledOutcome intent.operation = some outcome) &&
    decide (lateBatch.result.image.oauth = restartedWriter.oauth) &&
    decide (afterStagedBatch.result.image = afterStaged) &&
    decide (afterStagedBatch.result.pending = [intent.operation, intent.operation]) &&
    decide (Revocation.Crash.effectStatus afterStagedBatch.result.image intent.operation = .unresolved) &&
    decide (commitAgain.result.confirmed = [intent.operation]) &&
    (retiredWriterRun.stopped == some intent.operation) &&
    decide (retiredWriterRun.image = afterStaged) &&
    (retiredReplicaRun.stopped == some intent.operation) &&
    decide (retiredReplicaRun.image = afterStaged) &&
    decide (revokedThenHandedOff = lateRevoked) &&
    decide (takeoverPending.result.image = takeoverFinal) &&
    decide (takeoverPending.result.pending = [intent.operation, unrelated.operation]) &&
    decide (Revocation.Crash.effectStatus takeoverPending.result.image intent.operation = .unresolved) &&
    decide (takeoverRecovered.result.confirmed = [intent.operation, intent.operation]) &&
    decide (takeoverRecovered.result.image.settledOutcome intent.operation = some outcome) &&
    decide (takeoverRecovered.result.image.oauth = takeoverFinal.oauth) &&
    decide (stoppedSuffix = { committedPrefix with stopped := some unrelated.operation }) &&
    overlappingRecoveryExercise takeoverInput takeoverRecovered.result afterStagedBatch.result
      lateOriginal lateOther lateMissing retryAuthorization &&
    decide (lateRetried.result.image = finalLateWriter) &&
    decide (lateRetried.result.image.settledOutcome intent.operation = some outcome) &&
    decide (lateRetried.result.confirmed = [intent.operation, intent.operation]) &&
    decide (lateRetried.result.pending = [intent.operation, unrelated.operation]) &&
    decide (Revocation.Crash.effectStatus lateRetried.result.image unrelated.operation = .unresolved) &&
    (Revocation.Crash.begin { retryAuthorization with
      image := lateRetried.result.image, writer := 6, checkedWriter := 6 }).isNone &&
    lateRetried.result.stopped.isNone &&
    (staleLateBatch.run.stopped == some intent.operation) &&
    (staleRun.stopped == some unrelated.operation) &&
    staleRun.pending.isEmpty && staleRun.confirmed.isEmpty &&
    decide (staleRun.image = batchImage) &&
    decide (batch.result.confirmed = [intent.operation]) &&
    decide (batch.result.pending = [unrelated.operation]) &&
    batch.result.stopped.isNone &&
    decide (Revocation.Crash.effectStatus batch.result.image unrelated.operation = .unresolved) &&
    decide (rerunBatch.run.image = batch.result.image) &&
    (Revocation.Crash.reconcile legacyAudit).isNone &&
    (Receiver.reconcileManaged legacyRecovery).isNone &&
    (Receiver.migrateLegacy { migration with recovery := legacyConflict }).isNone &&
    (Receiver.migrateLegacy { migration with recovery := missingCommit }).isNone &&
    (Receiver.migrateLegacy { migration with recovery := foreignLegacy }).isNone &&
    decide (migrated.result.oauth = legacyImage.oauth) &&
    decide (migrated.result.settledOutcome intent.operation = some outcome) &&
    decide (Receiver.reconcileManaged migratedRecovery = some migrated.result) &&
    decide (Receiver.migrateLegacy { migration with recovery := migratedRecovery } = some migrated.result) &&
    (Receiver.migrateLegacy { migration with recovery := oldWriterRecovery }).isNone &&
    (Receiver.migrateLegacy { migration with recovery := oldReplicaRecovery }).isNone &&
    (Revocation.Crash.begin migratedRetry).isNone &&
    (Revocation.Crash.reconcile managedAudit).isNone &&
    (Receiver.reconcileManaged { anchored with audit := conflictAudit }).isNone &&
    (Receiver.reconcileManaged { anchored with placement := "standby" }).isNone &&
    (Receiver.reconcileManaged { anchored with independent := some foreignPin }).isNone &&
    decide (anchoredSettlement.result.settledOutcome intent.operation = some outcome) &&
    decide (Receiver.reconcileManaged { anchored with audit := anchoredRetry } = some anchoredSettlement.result) &&
    (Revocation.Crash.reconcile { conflictingEvidence with image := durableWithoutAck }).isNone &&
    decide (Revocation.Crash.reconcile confirmed = some postActive) &&
    (Revocation.Crash.reconcile { conflictingEvidence with image := postActive, writer := 4 }).isNone &&
    (Receiver.receiveManaged { unknownRetry with authorization :=
      { retryAuthorization with image := postActive, writer := 4, checkedWriter := 4 } }).isNone &&
    (Receiver.receiveManaged { unknownRetry with authorization :=
      { retryAuthorization with image := lateSettlement.result } }).isNone &&
    (Receiver.receiveManaged unknownRetry).isNone &&
    decide (Revocation.Crash.effectStatus settled.result intent.operation = .reconciled) &&
    decide (committed.result.receiver.image = delivered.result) &&
    decide (committed.result.oauth = managedStart.result) &&
    decide (successor.result.oauthAuthority = some authority) &&
    (Receiver.receiveManaged afterTakeover).isNone &&
    (Receiver.promote { promotion with independent := none }).isNone &&
    (Receiver.promote { promotion with candidate := receiver }).isNone &&
    (Receiver.promote { promotion with candidate := fork }).isNone &&
    decide (stagedPromotion = pin) &&
    (Receiver.promote contender).isNone &&
    decide (recovered.result = committedPromotion.image.cut) &&
    (Receiver.recoverPromotion { recovery with expected := committedPromotion }).isNone &&
    (Receiver.recoverPromotion ⟨some committedPromotion, pin, "primary", committedPromotion.image⟩).isNone &&
    decide (committedPromotion.active = "standby") &&
    decide (committedPromotion.image.cut.generation = restored.cut.generation + 1) &&
    (Receiver.receiveManaged { afterTakeover with placement := "primary", authorization := begin }).isNone &&
    (Receiver.receiveManaged { afterTakeover with authorization := begin }).isNone &&
    (Receiver.evidence staged dispatch.operation).isNone &&
    decide (restored.cut.generation = cut.generation + 1) &&
    (Receiver.receive { request with image := restored }).isNone &&
    (Receiver.receive retry).isNone &&
    (Receiver.receive { request with observedChannel := "channel-two" }).isNone &&
    (Receiver.receive { request with senderAuthenticated := false }).isNone &&
    decide (stale.oauth = handed.oauth) &&
    decide ((Refresh.RevocationInput.key ⟨durable.checkpoint.ledger, verified digest⟩) ∈ live.oauth.checkpoint.ledger.revoked) &&
    (Revocation.Crash.revoke handed 0 (verified digest)).isNone &&
    (Revocation.Crash.begin { begin with image := handed }).isNone &&
    (Revocation.Crash.begin { begin with image := handed, writer := 1, checkedWriter := 1 }).isNone &&
    (Revocation.Crash.reconcile { reconcile with outcomes := [] }).isNone &&
    (Revocation.Crash.reconcile { reconcile with outcomes := [{ outcome with signature := [8] }] }).isNone &&
    decide (settled.result.settledOutcome intent.operation = some outcome) &&
    decide (settled.result.oauth = live.oauth) &&
    (Revocation.Crash.begin { begin with image := settled.result, writer := 1, checkedWriter := 1 }).isNone

private def exercise (confirmation replacement : Confirmation) : Bool := Id.run do
  let parSender : PAR.ParSender := match confirmation with
    | .dpop key => .dpop (some key) none
    | .mtls _ => .mtls
  let request : PAR.Request := ⟨session, ["fhir"], ["patient.read"], parSender⟩
  let pushed : PAR.PushInput := ⟨{}, registration, verified request, "par", 10, 15⟩
  let .ok stored := PAR.pushContract.invoke PAR.preparePush pushed | return false
  let grant : Grant :=
    ⟨⟨"issuer", "subject", "client"⟩, ["fhir"], ["patient.read"], "initial", 10, 16, confirmation⟩
  let auth : PAR.AuthorizationInput :=
    ⟨stored.result, "par", session, "par", session.client, false, 11, "code", 15, grant⟩
  let .ok issued := PAR.authorizationContract.invoke PAR.prepareAuthorization auth | return false
  let code : Code.Request :=
    ⟨"code", session.issuer, session.client, session.redirect, session.state, session.browser, session.s256⟩
  let redeem : PAR.RedemptionInput auth :=
    ⟨issued, issued.result.ledger.codes, verified ⟨code, tokenSender confirmation⟩, 12⟩
  let .ok redeemed := (PAR.redemptionContract auth).invoke PAR.prepareRedemption redeem | return false
  let enrollment : Enrollment redeem := ⟨redeemed, {}, digest, 12, 40⟩
  let .ok enrolled := (enrollmentContract redeem).invoke prepareEnrollment enrollment | return false
  let initial := enrolled.result
  let next := { grant with tokenHash := "next", expiresAt := 30 }
  let exchange : RefreshInput := ⟨initial, verified ⟨digest, tokenSender confirmation⟩, next, 13⟩
  let .ok first := Refresh.contract.invoke Refresh.prepare exchange | return false
  let retry : RefreshInput := { exchange with ledger := first.result.2, next := { next with tokenHash := "second" } }
  let .ok second := Refresh.contract.invoke Refresh.prepare retry | return false
  let current := second.result.2
  let revocation : RevocationInput := ⟨current, verified digest⟩
  let .ok revoked := revokeContract.invoke prepareRevoke revocation | return false
  let authority : Authority := { activeGrants := [grant, first.result.1, second.result.1], now := 14, maxProofAge := 5 }
  let target : Target :=
    ⟨grant.identity, "fhir", ["patient.read"], "GET", "https://gateway.example/patient"⟩
  let sender (g : Grant) (binding : Confirmation) (proofId : String) : SenderObservation :=
    match binding with
    | .mtls peer => .mtls peer
    | .dpop key => .dpop ⟨key, target.method, target.uri, g.tokenHash, 14, proofId, true, true, false⟩
  let before : Revocation.Checkpoint := ⟨"issuer-ledger", 3, current⟩
  let frontier : Revocation.Checkpoint := ⟨before.authorityId, 4, revoked.result⟩
  let forged := { frontier with ledger := current }
  let durable : Revocation.Recovery.Store := ⟨before, []⟩
  let some persisted := durable.revoke (verified digest) | return false
  let recovery : Revocation.Recovery.RecoveryInput := ⟨before.authorityId, some persisted, frontier⟩
  let after : RefreshInput := { retry with ledger := current, next := { next with tokenHash := "after" } }
  return (Revocation.Recovery.recoveryContract.invoke Revocation.Recovery.prepareRecovery recovery).isOk &&
    (Revocation.Recovery.recover { recovery with replica := before }).isNone &&
    (Revocation.Recovery.recover { recovery with replica := forged }).isNone &&
    (Revocation.Recovery.recover { recovery with durable := none }).isNone &&
    (Revocation.Recovery.recover { recovery with authorityId := "another-authority" }).isNone &&
    (refresh { exchange with verified := verified ⟨digest, tokenSender replacement⟩ }).isNone &&
    (refresh { exchange with next := { next with confirmation := replacement } }).isNone &&
    (refresh { exchange with next := { next with scopes := ["patient.write"] } }).isNone &&
    (refresh { exchange with ledger := current }).isNone &&
    (refresh { retry with now := 40 }).isNone &&
    (enroll { enrollment with ledger := revoked.result, refreshDigest := ⟨"new-refresh"⟩ }).isNone &&
    (revoke { revocation with verified := { revocation.verified with client := "other" } }).isNone &&
    (refresh after).isSome &&
    (refresh { after with ledger := revoked.result }).isNone &&
    [grant, first.result.1, second.result.1].all (fun g =>
      let attempt : Attempt := ⟨g, target, sender g confirmation "same-attempt", true⟩
      (useAccess current authority attempt).isSome &&
      (useAccess current authority ⟨g, target, sender g replacement "changed", true⟩).isNone &&
      (useAccess revoked.result authority attempt).isNone &&
      let read : Revocation.FinalRead := ⟨⟨before, before, authority, attempt⟩, some before⟩
      let fork : Revocation.FinalRead := ⟨⟨forged, forged, authority, attempt⟩, some frontier⟩
      let renewed : Revocation.FinalRead := ⟨⟨frontier, frontier, authority, attempt⟩, some frontier⟩
      (Revocation.contract.invoke Revocation.prepare read).isOk &&
      (Revocation.check { read with independent := none }).isNone &&
      (Revocation.check { read with independent := some frontier }).isNone &&
      (Revocation.check fork).isNone &&
      (Revocation.check { renewed with checked := before }).isNone &&
      (Revocation.check renewed).isNone &&
      let input : Revocation.Recovery.FinalInput := ⟨before.authorityId, some durable, read.toReplicaRead⟩
      let result := Revocation.Recovery.finalContract.invoke Revocation.Recovery.prepareFinal input
      match result with
      | .error _ => false
      | .ok committed =>
        let replay := Revocation.Recovery.finalize { input with durable := some committed.result }
        let senderAcceptsReplay := match confirmation with
          | .dpop _ => replay.isNone
          | .mtls _ => replay.isSome
        crashExercise durable read.toReplicaRead && senderAcceptsReplay &&
          (Revocation.Recovery.finalize { input with durable := some persisted }).isNone &&
          (Revocation.Recovery.finalize
            ⟨before.authorityId, some persisted, renewed.toReplicaRead⟩).isNone)

/-- The identical request still passes with a pre-revocation snapshot even
when the authoritative revocation has already committed. -/
theorem stale_snapshot_counterexample_and_current_refusal :
    exercise (.dpop "key") (.dpop "replacement-key") = true ∧
    exercise (.mtls "cert") (.mtls "replacement-cert") = true := by native_decide

end Tests.Gateway.OAuthRefresh

#print axioms CedarPooSpec.Gateway.OAuth.Refresh.enrollment_retains_sender
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.refresh_preserves_sender
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.wrong_sender_refused
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.revocation_retains_lineage
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.revocation_blocks_refresh
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.revoked_family_blocks_resource_contract

#print axioms CedarPooSpec.Gateway.OAuth.Refresh.committed_run_preserves_revocation
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.committed_descendant_blocks_access
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.committed_descendant_blocks_refresh

#print axioms CedarPooSpec.Gateway.OAuth.Revocation.mediation_retains_original_and_frontier
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.revoked_descendant_refused
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.final_use_refused_without_current_check

#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Recovery.recovery_retains_independent_store
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Recovery.persisted_revocation_marks_family
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Recovery.final_retains_checkpoint_and_reservation
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Recovery.durable_revocation_blocks_final
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Recovery.durable_reservation_blocks_final
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Recovery.persisted_revoke_refuses_final

#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.durable_revoke_retains_marker
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.old_writer_fenced_after_handoff
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.begin_records_burn
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.reconciliation_preserves_burn_and_revocations
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.unclean_evidence_cannot_settle
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.settlement_cannot_reopen_operation

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.receive_retains_reservation_and_outcome
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.committed_cut_refuses_old_dispatch
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.cut_advance_keeps_no_resend
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.committed_receipt_recovered

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.promotion_retains_acknowledged_delivery
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.promotion_fences_previous_placement
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.promotion_keeps_signed_evidence
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.promoted_receiver_refuses_same_operation
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.fenced_placement_cannot_receive

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.promotion_cannot_consume_checkpoint_twice
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.committed_promotion_ack_can_recover
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.inactive_placement_cannot_recover_promotion

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.promotion_preserves_oauth_authority
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.consecutive_promotions_keep_signed_evidence
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.revoked_grant_cannot_receive
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.stale_oauth_replica_cannot_receive

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.reservation_without_receiver_commit
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.reserved_operation_refused_after_failover
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.handoff_preserves_effect_state
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.revocation_preserves_effect_state
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.missing_outcome_cannot_settle
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.effect_status_survives_failover
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.managed_retains_oauth_reservation
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.conflicting_outcome_cannot_replace_settlement

#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.serialized_conflict_cannot_win
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.committed_settlement_survives_recovery

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.conflict_first_cannot_settle
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.managed_reconciliation_pins_committed_outcome

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.foreign_receiver_cannot_migrate
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacy_migration_preserves_authority_and_burn
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.migration_pins_committed_outcome
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.missing_committed_outcome_refuses_migration

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.retired_replica_cannot_migrate
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.retired_writer_cannot_migrate

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_resume_prefix
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_preserves_authority
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_cannot_reopen_operation

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_stops_at_retired_replica
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_stopped_keeps_state

#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_stops_at_stale_receiver_image
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_pending_keeps_image
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.confirmed_migration_is_read_only
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.missing_committed_outcome_cannot_migrate
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_confirmed_keeps_image
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.staged_migration_cannot_reopen_operation
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.committed_migration_survives_takeover
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.revoke_and_handoff_agree
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_stops_at_retired_writer
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.committed_migration_cannot_reopen_after_failover
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_fenced_suffix_keeps_prefix
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_read_only_fold_keeps_image
#print axioms CedarPooSpec.Gateway.OAuth.Receiver.legacyBatch_read_only_crash_survives_takeovers
