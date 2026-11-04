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

/-- Replay identity shared by routes served by one authorization authority. -/
structure ProofKey where
  issuer : String
  thumbprint : String
  proofId : String
  deriving DecidableEq

/-- Current resource authority. The adapter serializes commit and revocation
against this image and supplies time from its trusted clock. -/
structure Authority where
  activeGrants : List Grant
  revokedTokens : List String := []
  reserved : List ProofKey := []
  now : Nat
  maxProofAge : Nat
  deriving DecidableEq

structure Attempt where
  grant : Grant
  target : Target
  sender : SenderObservation
  tokenAuthenticated : Bool

def Attempt.proofKey (attempt : Attempt) : Option ProofKey :=
  match attempt.sender with
  | .dpop proof => some ⟨attempt.grant.identity.issuer, proof.thumbprint, proof.proofId⟩
  | .mtls _ => none

def Authority.revoke (authority : Authority) (tokenHash : String) : Authority :=
  { authority with revokedTokens := tokenHash :: authority.revokedTokens }

/-- Project active status and replay eligibility from current authority, never
from a previously accepted request. The pending reservation is installed only
with a successful transition. -/
def Authority.observe (authority : Authority) (attempt : Attempt) : CurrentUse :=
  let sender := match attempt.sender with
    | .dpop proof =>
      let fresh := attempt.proofKey.all (fun key => decide (key ∉ authority.reserved))
      .dpop { proof with replayReserved := fresh }
    | .mtls peer => .mtls peer
  ⟨attempt.grant, attempt.target, sender, authority.now, authority.maxProofAge,
    attempt.tokenAuthenticated,
    decide (attempt.grant ∈ authority.activeGrants ∧
      attempt.grant.tokenHash ∉ authority.revokedTokens)⟩

/-- A pure commit proposal for the OAuth component of final admission.
Cedar and the remaining Zero Trust requirements still govern the effect. -/
def Authority.commit (authority : Authority) (attempt : Attempt) : Option Authority :=
  if (authority.observe attempt).bound then
    some { authority with reserved := match attempt.proofKey with
      | none => authority.reserved
      | some key => key :: authority.reserved }
  else none

def commitContract : Contract Unit (Authority × Attempt) Authority where
  input := ⟨"current-oauth-authority", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"oauth-admission-successor", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input next => input.1.commit input.2 = some next
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareCommit (input : Authority × Attempt) : Except String (Authority × Unit) :=
  match input.1.commit input.2 with
  | some next => .ok (next, ())
  | none => .error "OAuth admission refused"

theorem commit_preserves_reservation
    (receipt : Invocation commitContract prepareCommit (authority, attempt))
    (key : ProofKey) (dpop : attempt.proofKey = some key) :
    key ∈ receipt.result.reserved := by
  have committed := receipt.logic
  change authority.commit attempt = some receipt.result at committed
  unfold Authority.commit at committed
  split at committed
  · rw [← Option.some.inj committed]
    simp [dpop]
  · contradiction

theorem reserved_proof_refused (authority : Authority) (attempt : Attempt)
    (key : ProofKey) (dpop : attempt.proofKey = some key) (used : key ∈ authority.reserved) :
    authority.commit attempt = none := by
  cases h : attempt.sender with
  | mtls peer => simp [Attempt.proofKey, h] at dpop
  | dpop proof =>
    cases binding : attempt.grant.confirmation <;>
      simp [Authority.commit, Authority.observe, CurrentUse.bound, CurrentUse.senderBound,
        h, binding, dpop, used]

theorem revoked_token_refused (authority : Authority) (attempt : Attempt)
    (revoked : attempt.grant.tokenHash ∈ authority.revokedTokens) :
    authority.commit attempt = none := by
  simp [Authority.commit, Authority.observe, CurrentUse.bound, revoked]

theorem revoke_blocks_next_use (authority : Authority) (attempt : Attempt) :
    (authority.revoke attempt.grant.tokenHash).commit attempt = none := by
  apply revoked_token_refused
  simp [Authority.revoke]

theorem commit_preserves_revocations
    (receipt : Invocation commitContract prepareCommit (authority, attempt)) :
    receipt.result.revokedTokens = authority.revokedTokens := by
  have committed := receipt.logic
  change authority.commit attempt = some receipt.result at committed
  unfold Authority.commit at committed
  split at committed
  · rw [← Option.some.inj committed]
  · contradiction

theorem same_proof_refused_after_commit
    (receipt : Invocation commitContract prepareCommit (authority, attempt))
    (key : ProofKey) (dpop : attempt.proofKey = some key)
    (retry : Attempt) (sameProof : retry.proofKey = some key) :
    receipt.result.commit retry = none :=
  reserved_proof_refused _ retry key sameProof (commit_preserves_reservation receipt key dpop)

end CedarPooSpec.Gateway.OAuth
