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

private def crashExercise (durable : Revocation.Recovery.Store)
    (read : Revocation.ReplicaRead) : Bool := Id.run do
  let openRevocation : Revocation.Crash.Image := { oauth := durable }
  let intent : CedarPooSpec.Gateway.EffectProtocol.CommitRef := ⟨"effect", [1], [2]⟩
  let history : Revocation.Crash.History :=
    ⟨"log", [intent], true, some (CedarPooSpec.Gateway.Lifecycle.WitnessFrontier.observe "log" [intent])⟩
  let begin : Revocation.Crash.BeginInput :=
    ⟨openRevocation, 0, 0, read, intent.operation, intent, "provider", history⟩
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
  let some advanced := Receiver.advance delivered.result cut | return false
  let restored := Revocation.Crash.recoverImage .durable delivered.result advanced
  let staged := Revocation.Crash.recoverImage .staged receiver delivered.result
  let some (action, outcome) := Receiver.evidence restored dispatch.operation | return false
  let newDispatch := { dispatch with cut := restored.cut }
  let retry : Receiver.Input := ⟨restored, ⟨newDispatch, "channel-two", outcome⟩,
    newDispatch, "channel-two", intent, true⟩
  let reconcile : Revocation.Crash.ReconcileInput := ⟨live, 1, intent.operation, trust, source, history, [action], [outcome]⟩
  let .ok settled := Revocation.Crash.reconcileContract.invoke Revocation.Crash.prepareReconcile reconcile | return false
  return (Receiver.evidence staged dispatch.operation).isNone &&
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
    (settled.result.resolved.any (fun entry => decide (entry = intent))) &&
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
