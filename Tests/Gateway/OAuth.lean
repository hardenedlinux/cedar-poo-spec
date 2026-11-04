import CedarPooSpec.Gateway.OAuth
import CedarPooSpec.Platform.AWS.AgentCore.Gateway
import CedarPooSpec.Vertical.Health.FHIR.ConsumerAccess

namespace Tests.Gateway.OAuth
open CedarPooSpec.Gateway.OAuth

private def actor : Identity := ⟨"https://issuer.example", "agent", "agent-client"⟩
private def target : Target := ⟨actor, "payments", ["approve"], "POST", "https://gateway.example/pay"⟩
private def grant : Grant := ⟨actor, ["payments"], ["approve"], "token-digest", 10, 20, .dpop "key"⟩
private def proof : DPoPObservation :=
  ⟨"key", "POST", "https://gateway.example/pay", "token-digest", 13, "proof-1", true, true, true⟩
private def current : CurrentUse := ⟨grant, target, .dpop proof, 14, 5, true, true⟩

theorem exact_dpop_is_accepted : (prepare current).isOk = true := by native_decide

theorem oauth_cannot_cross_resource_scope_or_identity :
    (prepare { current with target := { target with audience := "records" } }).isOk = false ∧
    (prepare { current with target := { target with requiredScopes := ["refund"] } }).isOk = false ∧
    (prepare { current with target := { target with identity := { actor with issuer := "other" } } }).isOk = false ∧
    (prepare { current with target := { target with identity := { actor with client := "other" } } }).isOk = false := by
  native_decide

theorem dpop_cannot_be_replayed_or_substituted :
    (prepare { current with sender := .dpop { proof with replayReserved := false } }).isOk = false ∧
    (prepare { current with sender := .dpop { proof with nonceSatisfied := false } }).isOk = false ∧
    (prepare { current with sender := .dpop { proof with tokenHash := "other" } }).isOk = false ∧
    (prepare { current with sender := .dpop { proof with method := "GET" } }).isOk = false ∧
    (prepare { current with sender := .dpop { proof with uri := "https://gateway.example/refund" } }).isOk = false ∧
    (prepare { current with sender := .dpop { proof with thumbprint := "other" } }).isOk = false ∧
    (prepare { current with sender := .dpop { proof with issuedAt := 15 } }).isOk = false ∧
    (prepare { current with now := 19 }).isOk = false := by
  native_decide

theorem rejects_unverified_inactive_and_expired_grants :
    (prepare { current with tokenAuthenticated := false }).isOk = false ∧
    (prepare { current with active := false }).isOk = false ∧
    (prepare { current with now := 20 }).isOk = false := by
  native_decide

theorem mtls_requires_the_authenticated_peer :
    let bound := { current with grant := { grant with confirmation := .mtls "cert" } }
    (prepare { bound with sender := .mtls "cert" }).isOk = true ∧
    (prepare { bound with sender := .mtls "other" }).isOk = false ∧
    (prepare bound).isOk = false := by
  native_decide

theorem profiles_use_the_same_oauth_requirement
    (base : CedarPooSpec.ZeroTrust.Framework E V) (observe : E → V → CurrentUse) :
    CedarPooSpec.Platform.AWS.AgentCore.withOAuth base observe =
      CedarPooSpec.Vertical.Health.FHIR.withOAuth base observe := rfl

end Tests.Gateway.OAuth

#print axioms CedarPooSpec.Gateway.OAuth.receipt_requires_current_bound_token
#print axioms CedarPooSpec.Gateway.OAuth.strengthened_preserves_gateway
#print axioms CedarPooSpec.Gateway.OAuth.revoked_grant_blocks_continuing_use
