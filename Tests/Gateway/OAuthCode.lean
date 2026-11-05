import CedarPooSpec.Gateway.OAuthCode

namespace Tests.Gateway.OAuthCode
open CedarPooSpec.Gateway.OAuth
open CedarPooSpec.Gateway.OAuth.Code

private def identity : Identity := ⟨"issuer", "subject", "client"⟩
private def grant : Grant := ⟨identity, ["fhir"], ["patient.read"], "token-hash", 10, 20, .mtls "cert"⟩
private def session : Session := ⟨"issuer", "client", "https://client.example/callback", "state", "browser",
  "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM"⟩
private def request : Request := ⟨"code", "issuer", "client", session.redirect, "state", "browser", session.s256⟩
private def item : Issued := ⟨"code", session, grant, 15⟩
private def input : Input := ⟨{ issued := [item] }, session, request, 12⟩
private def attempt : Attempt :=
  ⟨grant, ⟨identity, "fhir", ["patient.read"], "GET", "https://gateway.example/patient"⟩, .mtls "cert", true⟩
private def authority : Authority := { activeGrants := [grant], now := 12, maxProofAge := 5 }

theorem mismatches_are_refused :
    redeem { input with request := { request with responseIssuer := "other" } } = none ∧
    redeem { input with request := { request with redirect := session.redirect ++ "?x=1" } } = none ∧
    redeem { input with request := { request with browser := "other" } } = none ∧
    redeem { input with request := { request with state := "other" } } = none ∧
    redeem { input with request := { request with client := "other" } } = none ∧
    redeem { input with request := { request with verifierS256 := "other" } } = none ∧
    redeem { input with now := 15 } = none ∧
    redeem { input with ledger := { issued := [item, item] } } = none := by
  native_decide

theorem redeemed_code_and_current_resource_checks :
    (redeem input).isSome = true ∧
    (redeem input).bind (fun result => redeem { input with ledger := result.2 }) = none ∧
    ((redeem input).bind fun result => useRedeemed result.1 authority attempt).isSome = true ∧
    (redeem input).bind (fun result =>
      useRedeemed result.1 (authority.revoke grant.tokenHash) attempt) = none := by
  native_decide

end Tests.Gateway.OAuthCode

#print axioms CedarPooSpec.Gateway.OAuth.Code.redemption_retains_binding
#print axioms CedarPooSpec.Gateway.OAuth.Code.redeemed_code_cannot_be_reused
#print axioms CedarPooSpec.Gateway.OAuth.Code.redeemed_grant_still_obeys_revocation
#print axioms CedarPooSpec.Gateway.OAuth.Code.redeemed_resource_preserves_gateway
#print axioms CedarPooSpec.Gateway.OAuth.Code.redeemed_resource_rejects_revoked_use
