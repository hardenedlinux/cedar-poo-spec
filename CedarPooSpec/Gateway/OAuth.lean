import CedarPooSpec.ZeroTrust.Composition
import LeanPoo.Functional.DeclarativeMetadata

/-! Resource-side OAuth admission for a sender-constrained Gateway profile.
The Host authenticates token and proof bytes and derives the actual request.
This module checks their binding and strengthens existing Zero Trust admission. -/
namespace CedarPooSpec.Gateway.OAuth
open LeanPoo.Functional.DeclarativeMetadata

structure Identity where
  issuer : String
  subject : String
  client : String
  deriving DecidableEq

inductive Confirmation where
  | dpop (keyThumbprint : String)
  | mtls (certificateThumbprint : String)
  deriving DecidableEq

structure Grant where
  identity : Identity
  audiences : List String
  scopes : List String
  tokenHash : String
  notBefore : Nat
  expiresAt : Nat
  confirmation : Confirmation
  deriving DecidableEq

/-- Expected identity, audience and scopes come from Gateway authority and
routing. Method and URI come from the effective inbound request. -/
structure Target where
  identity : Identity
  audience : String
  requiredScopes : List String
  method : String
  uri : String
  deriving DecidableEq

structure DPoPObservation where
  thumbprint : String
  method : String
  uri : String
  tokenHash : String
  issuedAt : Nat
  proofId : String
  signatureVerified : Bool
  nonceSatisfied : Bool
  replayReserved : Bool

inductive SenderObservation where
  | dpop (proof : DPoPObservation)
  | mtls (authenticatedThumbprint : String)

structure CurrentUse where
  grant : Grant
  target : Target
  sender : SenderObservation
  now : Nat
  maxProofAge : Nat
  tokenAuthenticated : Bool
  active : Bool

def CurrentUse.senderBound (use : CurrentUse) : Prop :=
  match use.grant.confirmation, use.sender with
  | .dpop key, .dpop proof =>
    proof.signatureVerified = true ∧ proof.nonceSatisfied = true ∧
      proof.replayReserved = true ∧ proof.proofId ≠ "" ∧ key ≠ "" ∧
      proof.thumbprint = key ∧ proof.method = use.target.method ∧
      proof.uri = use.target.uri ∧ proof.tokenHash = use.grant.tokenHash ∧
      proof.issuedAt ≤ use.now ∧ use.now - proof.issuedAt ≤ use.maxProofAge
  | .mtls certificate, .mtls observed => certificate ≠ "" ∧ observed = certificate
  | _, _ => False

instance (use : CurrentUse) : Decidable use.senderBound := by
  unfold CurrentUse.senderBound
  split <;> infer_instance

def CurrentUse.bound (use : CurrentUse) : Prop :=
  use.tokenAuthenticated = true ∧ use.active = true ∧
    use.grant.identity = use.target.identity ∧ use.target.audience ≠ "" ∧
    use.target.audience ∈ use.grant.audiences ∧
    use.target.requiredScopes.all (fun scope => use.grant.scopes.contains scope) = true ∧
    use.grant.tokenHash ≠ "" ∧
    use.grant.notBefore ≤ use.now ∧ use.now < use.grant.expiresAt ∧ use.senderBound

instance (use : CurrentUse) : Decidable use.bound := by
  unfold CurrentUse.bound
  infer_instance

/-- The receipt records checked OAuth evidence for this use. Existing Cedar
authorization, durable consumption and final mediation remain required. -/
def contract : Contract Unit CurrentUse Unit where
  input := ⟨"host-observed-oauth-use", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"bound-oauth-use", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ use _ => use.bound
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (use : CurrentUse) : Except String (Unit × Unit) :=
  if use.bound then .ok ((), ()) else .error "OAuth use refused"

theorem receipt_requires_current_bound_token (receipt : Invocation contract prepare use) :
    use.bound := receipt.logic

theorem inactive_refused (use : CurrentUse) (inactive : use.active = false) :
    prepare use = .error "OAuth use refused" := by
  simp [prepare, CurrentUse.bound, inactive]

theorem wrong_audience_refused (use : CurrentUse)
    (wrong : use.target.audience ∉ use.grant.audiences) :
    prepare use = .error "OAuth use refused" := by
  simp [prepare, CurrentUse.bound, wrong]

theorem expired_refused (use : CurrentUse) (expired : use.grant.expiresAt ≤ use.now) :
    prepare use = .error "OAuth use refused" := by
  simp [prepare, CurrentUse.bound, Nat.not_lt_of_ge expired]

def strengthen (base : CedarPooSpec.ZeroTrust.Framework E V) (observe : E → V → CurrentUse) :=
  base.withRequirement (fun effect actual => (observe effect actual).bound)

theorem strengthened_preserves_gateway
    (base : CedarPooSpec.ZeroTrust.Framework E V) (observe : E → V → CurrentUse)
    (accepted : (strengthen base observe).required effect actual) :
    base.required effect actual :=
  CedarPooSpec.ZeroTrust.with_requirement_preserves_framework base _ _ _ accepted

theorem strengthened_requires_fresh_oauth
    (base : CedarPooSpec.ZeroTrust.Framework E V) (observe : E → V → CurrentUse)
    (accepted : (strengthen base observe).required effect actual) :
    (observe effect actual).bound :=
  accepted.2.1.2

theorem revoked_grant_blocks_continuing_use
    (base : CedarPooSpec.ZeroTrust.Framework E V) (observe : E → V → CurrentUse)
    (inactive : (observe effect actual).active = false) :
    ¬ (strengthen base observe).required effect actual := by
  intro accepted
  have active := (strengthened_requires_fresh_oauth base observe accepted).2.1
  simp [inactive] at active

end CedarPooSpec.Gateway.OAuth
