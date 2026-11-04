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
private def request : Request := ⟨session, ["fhir"], ["patient.read"]⟩
private def pushed : PushInput := ⟨{}, registration, verified request, "par", 10, 15⟩
private def grant : Grant :=
  ⟨⟨"issuer", "subject", "client"⟩, ["fhir"], ["patient.read"], "token-hash", 10, 20, .mtls "cert"⟩
private def authorization (ledger : Ledger) : AuthorizationInput :=
  ⟨ledger, "par", session, "par", session.client, false, 12, "code", 17, grant⟩
private def token : Code.Request :=
  ⟨"code", session.issuer, session.client, session.redirect, session.state, session.browser, session.s256⟩

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
  return (authorize { input with uri := "replacement" }).isNone &&
    (authorize { input with client := "other" }).isNone &&
    (authorize { input with session := { session with issuer := "other" } }).isNone &&
    (authorize { input with session := { session with browser := "other" } }).isNone &&
    (authorize { input with hasExtraParameters := true }).isNone &&
    (authorize { input with now := 15 }).isNone &&
    (authorize { input with grant := { grant with scopes := ["patient.write"] } }).isNone &&
    (authorize { input with ledger := result.ledger }).isNone &&
    (push { pushed with ledger := result.ledger }).isNone

example : authorizationChecks = true := by native_decide

private def redemptionChecks : Bool := Id.run do
  let .ok stored := pushContract.invoke preparePush pushed | return false
  let ledger := stored.result
  let .ok receipt := authorizationContract.invoke prepareAuthorization (authorization ledger) | return false
  let input : RedemptionInput (authorization ledger) := ⟨receipt, receipt.result.ledger.codes, verified token, 13⟩
  let .ok redeemed := (redemptionContract (authorization ledger)).invoke prepareRedemption input | return false
  let authority : Authority := { activeGrants := [grant], now := 13, maxProofAge := 5 }
  let attempt : Attempt :=
    ⟨grant, ⟨grant.identity, "fhir", ["patient.read"], "GET", "https://gateway.example/patient"⟩, .mtls "cert", true⟩
  return (redeem { input with verified := { input.verified with client := "other" } }).isNone &&
    (redeem { input with verified := { input.verified with credential := .mtls "replacement" } }).isNone &&
    (redeem { input with verified := verified { token with responseIssuer := "other" } }).isNone &&
    (redeem { input with verified := verified { token with verifierS256 := "replacement" } }).isNone &&
    (redeem { input with ledger := redeemed.result.2 }).isNone &&
    (Code.useRedeemed redeemed.result.1 authority attempt).isSome &&
    (Code.useRedeemed redeemed.result.1 (authority.revoke grant.tokenHash) attempt).isNone

example : redemptionChecks = true := by native_decide

end Tests.Gateway.OAuthPAR

#print axioms CedarPooSpec.Gateway.OAuth.PAR.push_retains_request
#print axioms CedarPooSpec.Gateway.OAuth.PAR.authorization_retains_binding
#print axioms CedarPooSpec.Gateway.OAuth.PAR.authorized_reference_cannot_be_reused
#print axioms CedarPooSpec.Gateway.OAuth.PAR.redemption_retains_binding
#print axioms CedarPooSpec.Gateway.OAuth.PAR.redeemed_grant_respects_pushed_request
#print axioms CedarPooSpec.Gateway.OAuth.PAR.redeemed_code_cannot_be_reused
#print axioms CedarPooSpec.Gateway.OAuth.PAR.resource_rejects_revoked_grant
