import CedarPooSpec.Gateway.OAuthPAR

namespace Tests.Gateway.OAuthPAR
open CedarPooSpec.Gateway.OAuth
open CedarPooSpec.Gateway.OAuth.PAR

private def session : Code.Session :=
  ⟨"issuer", "client", "https://client.example/callback", "state", "browser",
    "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM"⟩
private def registration : Registration := ⟨session.issuer, session.client, .mtls "cert", [session.redirect], ["patient.read"]⟩
private def verified (request : α) : VerifiedClient α :=
  ⟨registration.issuer, registration.client, registration.credential, request⟩
private def request : Request := ⟨session, ["fhir"], ["patient.read"], .mtls⟩
private def pushed : PushInput := ⟨{}, registration, verified request, "par", 10, 15⟩
private def grant : Grant :=
  ⟨⟨"issuer", "subject", "client"⟩, ["fhir"], ["patient.read"], "token-hash", 10, 20, .mtls "cert"⟩
private def authorization (ledger : Ledger) : AuthorizationInput :=
  ⟨ledger, "par", session, "par", session.client, false, 12, "code", 17, grant⟩
private def codeRequest : Code.Request :=
  ⟨"code", session.issuer, session.client, session.redirect, session.state, session.browser, session.s256⟩
private def token : TokenRequest := ⟨codeRequest, .mtls "cert"⟩

example :
    push { pushed with verified := { pushed.verified with issuer := "other" } } = none ∧
    push { pushed with verified := { pushed.verified with client := "other" } } = none ∧
    push { pushed with verified := { pushed.verified with credential := .privateKeyJwt "cert" } } = none ∧
    push { pushed with registration := { registration with scopes := [] } } = none ∧
    push { pushed with expiresAt := 610 } = none := by native_decide

private def authorizationChecks : Bool := Id.run do
  let some ledger := push pushed | return false
  let some ledger := push { pushed with ledger, uri := "replacement" } | return false
  let input := authorization ledger
  let some result := authorize input | return false
  return (authorize { input with codeExpiresAt := input.now + 60 }).isSome &&
    (authorize { input with codeExpiresAt := input.now + 61 }).isNone &&
    (authorize { input with codeExpiresAt := input.now }).isNone &&
    (authorize { input with uri := "replacement" }).isNone &&
    (authorize { input with client := "other" }).isNone &&
    (authorize { input with session := { session with issuer := "other" } }).isNone &&
    (authorize { input with session := { session with browser := "other" } }).isNone &&
    (authorize { input with hasExtraParameters := true }).isNone &&
    (authorize { input with now := 15 }).isNone &&
    (authorize { input with grant := { grant with scopes := ["patient.write"] } }).isNone &&
    (authorize { input with ledger := result.ledger }).isNone &&
    (push { pushed with ledger := result.ledger }).isNone

example : authorizationChecks = true := by native_decide

private def redemptionChecks (credential : Credential) : Bool := Id.run do
  let registration := { registration with credential }
  let verified := fun {α} (request : α) => VerifiedClient.mk registration.issuer registration.client credential request
  let pushInput := { pushed with registration, verified := verified request }
  let .ok stored := pushContract.invoke preparePush pushInput | return false
  let ledger := stored.result
  let .ok receipt := authorizationContract.invoke prepareAuthorization (authorization ledger) | return false
  let input : RedemptionInput (authorization ledger) := ⟨receipt, receipt.result.ledger.codes, verified token, 13⟩
  let .ok redeemed := (redemptionContract (authorization ledger)).invoke prepareRedemption input | return false
  let authority : Authority := { activeGrants := [grant], now := 13, maxProofAge := 5 }
  let attempt : Attempt :=
    ⟨grant, ⟨grant.identity, "fhir", ["patient.read"], "GET", "https://gateway.example/patient"⟩, .mtls "cert", true⟩
  return (redeem { input with verified := { input.verified with client := "other" } }).isNone &&
    (redeem { input with verified := { input.verified with credential := .mtls "replacement" } }).isNone &&
    (redeem { input with verified := verified { token with redemption := { codeRequest with responseIssuer := "other" } } }).isNone &&
    (redeem { input with verified := verified { token with redemption := { codeRequest with verifierS256 := "replacement" } } }).isNone &&
    (redeem { input with verified := verified { token with sender := .mtls "other-peer" } }).isNone &&
    (redeem { input with ledger := redeemed.result.2 }).isNone &&
    (Code.useRedeemed redeemed.result.1 authority attempt).isSome &&
    (Code.useRedeemed redeemed.result.1 authority { attempt with sender := .mtls "other-peer" }).isNone &&
    (Code.useRedeemed redeemed.result.1 (authority.revoke grant.tokenHash) attempt).isNone

example :
    redemptionChecks (.mtls "cert") = true ∧
    redemptionChecks (.privateKeyJwt "client-key") = true ∧
    (TokenSender.mtls "other-peer").matches (.mtls "cert") (.mtls "other-peer") = false := by
  native_decide

private def dpopChecks (sender : ParSender) : Bool := Id.run do
  let pushInput := { pushed with verified := verified { request with sender } }
  let .ok stored := pushContract.invoke preparePush pushInput | return false
  let requested := { grant with confirmation := .dpop "key" }
  let authorization := { authorization stored.result with grant := requested }
  let .ok receipt := authorizationContract.invoke prepareAuthorization authorization | return false
  let token := { token with sender := .dpop ⟨"key"⟩ }
  let input : RedemptionInput authorization := ⟨receipt, receipt.result.ledger.codes, verified token, 13⟩
  let .ok redeemed := (redemptionContract authorization).invoke prepareRedemption input | return false
  let authority : Authority := { activeGrants := [requested], now := 13, maxProofAge := 5 }
  let target : Target :=
    ⟨grant.identity, "fhir", ["patient.read"], "GET", "https://gateway.example/patient"⟩
  let proof : DPoPObservation :=
    ⟨"key", target.method, target.uri, grant.tokenHash, 13, "proof", true, true, false⟩
  let attempt : Attempt := ⟨requested, target, .dpop proof, true⟩
  return (authorize { authorization with grant := { requested with confirmation := .dpop "other" } }).isNone &&
    (authorize { authorization with grant }).isNone &&
    (redeem { input with verified := verified { token with sender := .dpop ⟨"other"⟩ } }).isNone &&
    (redeem { input with verified := verified { token with sender := .mtls "cert" } }).isNone &&
    (Code.useRedeemed redeemed.result.1 authority attempt).isSome &&
    (Code.useRedeemed redeemed.result.1 authority
      { attempt with sender := .dpop { proof with thumbprint := "other" } }).isNone &&
    (Code.useRedeemed redeemed.result.1 (authority.revoke grant.tokenHash)
      { attempt with sender := .dpop { proof with proofId := "fresh" } }).isNone

example :
    dpopChecks (.dpop (some "key") none) = true ∧
    dpopChecks (.dpop none (some ⟨"key"⟩)) = true ∧
    dpopChecks (.dpop (some "key") (some ⟨"key"⟩)) = true ∧
    push { pushed with verified := verified {
      request with sender := .dpop (some "key") (some ⟨"other"⟩) } } = none ∧
    push { pushed with verified := verified { request with sender := .dpop none none } } = none := by
  native_decide

end Tests.Gateway.OAuthPAR

#print axioms CedarPooSpec.Gateway.OAuth.PAR.push_retains_request
#print axioms CedarPooSpec.Gateway.OAuth.PAR.authorization_retains_binding
#print axioms CedarPooSpec.Gateway.OAuth.PAR.authorized_reference_cannot_be_reused
#print axioms CedarPooSpec.Gateway.OAuth.PAR.redemption_retains_binding
#print axioms CedarPooSpec.Gateway.OAuth.PAR.redeemed_grant_respects_pushed_request
#print axioms CedarPooSpec.Gateway.OAuth.PAR.redeemed_code_cannot_be_reused
#print axioms CedarPooSpec.Gateway.OAuth.PAR.resource_rejects_revoked_grant

#print axioms CedarPooSpec.Gateway.OAuth.PAR.redeemed_dpop_key
#print axioms CedarPooSpec.Gateway.OAuth.PAR.redeemed_mtls_certificate
#print axioms CedarPooSpec.Gateway.OAuth.PAR.wrong_token_sender_refused
#print axioms CedarPooSpec.Gateway.OAuth.PAR.resource_requires_redeemed_sender

#print axioms CedarPooSpec.Gateway.OAuth.PAR.resource_matches_confirmation
#print axioms CedarPooSpec.Gateway.OAuth.PAR.resource_preserves_par_dpop_key
