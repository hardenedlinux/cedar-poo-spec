import CedarPooSpec.Gateway.OAuthRefresh

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
  return (refresh { exchange with verified := verified ⟨digest, tokenSender replacement⟩ }).isNone &&
    (refresh { exchange with next := { next with confirmation := replacement } }).isNone &&
    (refresh { exchange with next := { next with scopes := ["patient.write"] } }).isNone &&
    (refresh { exchange with ledger := current }).isNone &&
    (refresh { retry with now := 40 }).isNone &&
    (enroll { enrollment with ledger := revoked.result, refreshDigest := ⟨"new-refresh"⟩ }).isNone &&
    (revoke { revocation with verified := { revocation.verified with client := "other" } }).isNone &&
    (refresh { retry with ledger := revoked.result, next := { next with tokenHash := "after" } }).isNone &&
    [grant, first.result.1, second.result.1].all (fun g =>
      (useAccess current authority ⟨g, target, sender g confirmation "before", true⟩).isSome &&
      (useAccess current authority ⟨g, target, sender g replacement "changed", true⟩).isNone &&
      (useAccess revoked.result authority ⟨g, target, sender g confirmation "fresh", true⟩).isNone)

example :
    exercise (.dpop "key") (.dpop "replacement-key") = true ∧
    exercise (.mtls "cert") (.mtls "replacement-cert") = true := by native_decide

end Tests.Gateway.OAuthRefresh

#print axioms CedarPooSpec.Gateway.OAuth.Refresh.enrollment_retains_sender
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.refresh_preserves_sender
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.wrong_sender_refused
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.revocation_retains_lineage
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.revocation_blocks_refresh
#print axioms CedarPooSpec.Gateway.OAuth.Refresh.revoked_family_blocks_resource_contract
