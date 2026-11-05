import CedarPooSpec.Gateway.OAuth

/-! Authorization-code redemption for the upstream OAuth library.
The trusted client selects the issuer and stores the pending browser session.
The authorization server supplies the code record and verified token result. -/
namespace CedarPooSpec.Gateway.OAuth.Code
open LeanPoo.Functional.DeclarativeMetadata

structure Session where
  issuer : String
  client : String
  redirect : String
  state : String
  browser : String
  s256 : String
  deriving DecidableEq

structure Issued where
  code : String
  session : Session
  grant : Grant
  expiresAt : Nat
  deriving DecidableEq

structure Request where
  code : String
  responseIssuer : String
  client : String
  redirect : String
  state : String
  browser : String
  verifierS256 : String
  deriving DecidableEq

abbrev CodeKey := String × String

structure Ledger where
  issued : List Issued
  spent : List CodeKey := []
  deriving DecidableEq

/-- The issuer component is the selected authorization server, never a
redirect parameter used to choose the token endpoint. -/
def Ledger.lookup (ledger : Ledger) (session : Session) (code : String) : Option Issued :=
  match ledger.issued.filter (fun item => item.code == code && item.session.issuer == session.issuer) with
  | [item] => some item
  | _ => none

def bound (session : Session) (request : Request) (item : Issued) (now : Nat) : Prop :=
  session.issuer ≠ "" ∧ session.client ≠ "" ∧ session.redirect ≠ "" ∧
  session.state ≠ "" ∧ session.browser ≠ "" ∧ session.s256 ≠ "" ∧ request.code ≠ "" ∧
  item.session = session ∧ request.responseIssuer = session.issuer ∧
  request.client = session.client ∧ request.redirect = session.redirect ∧
  request.state = session.state ∧ request.browser = session.browser ∧
  request.verifierS256 = session.s256 ∧ now < item.expiresAt ∧
  item.grant.identity.issuer = session.issuer ∧ item.grant.identity.client = session.client

instance (session : Session) (request : Request) (item : Issued) (now : Nat) :
    Decidable (bound session request item now) := by unfold bound; infer_instance

structure Input where
  ledger : Ledger
  session : Session
  request : Request
  now : Nat

def Input.key (input : Input) : CodeKey := (input.session.issuer, input.request.code)

def redeem (input : Input) : Option (Grant × Ledger) := do
  let item ← input.ledger.lookup input.session input.request.code
  if input.key ∉ input.ledger.spent ∧ bound input.session input.request item input.now then
    some (item.grant, { input.ledger with spent := input.key :: input.ledger.spent })
  else none

def contract : Contract Unit Input (Grant × Ledger) where
  input := ⟨"selected-issuer-and-pending-session", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"redeemed-grant-and-spent-code", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => redeem input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : Input) : Except String ((Grant × Ledger) × Unit) :=
  match redeem input with
  | some result => .ok (result, ())
  | none => .error "OAuth code redemption refused"

theorem redemption_retains_binding
    (receipt : Invocation contract prepare input) :
    ∃ item, input.ledger.lookup input.session input.request.code = some item ∧
      bound input.session input.request item input.now ∧
      receipt.result.1 = item.grant ∧ input.key ∈ receipt.result.2.spent := by
  have accepted := receipt.logic
  change redeem input = some receipt.result at accepted
  cases found : input.ledger.lookup input.session input.request.code with
  | none => simp [redeem, found] at accepted
  | some item =>
    by_cases valid : input.key ∉ input.ledger.spent ∧ bound input.session input.request item input.now
    · simp [redeem, found, valid] at accepted
      rw [← accepted]
      exact ⟨item, rfl, valid.2, rfl, by simp⟩
    · simp [redeem, found, valid] at accepted

theorem spent_code_refused (input : Input) (spent : input.key ∈ input.ledger.spent) :
    redeem input = none := by
  cases found : input.ledger.lookup input.session input.request.code <;>
    simp [redeem, found, spent]

theorem redeemed_code_cannot_be_reused (receipt : Invocation contract prepare input)
    (retry : Input) (sameKey : retry.key = input.key)
    (currentLedger : retry.ledger = receipt.result.2) : redeem retry = none := by
  obtain ⟨_, _, _, _, spent⟩ := redemption_retains_binding receipt
  apply spent_code_refused
  simpa only [sameKey, currentLedger] using spent

/-- Redemption supplies provenance for the grant. Resource authorization
still uses the actual current authority and checks revocation and possession. -/
def useRedeemed (grant : Grant) (authority : Authority) (attempt : Attempt) : Option Authority :=
  if attempt.grant = grant then authority.commit attempt else none

theorem redeemed_grant_still_obeys_revocation (grant : Grant) (authority : Authority)
    (attempt : Attempt) (revoked : attempt.grant.tokenHash ∈ authority.revokedTokens) :
    useRedeemed grant authority attempt = none := by
  simp [useRedeemed, revoked_token_refused authority attempt revoked]

/-- Add redemption provenance to the existing resource-side refinement.
The actual deciding view supplies the current authority and effect attempt. -/
def strengthenResource
    (base : CedarPooSpec.ZeroTrust.Framework E V)
    (receipt : Invocation contract prepare input)
    (observe : E → V → Authority × Attempt) :=
  base.withRequirement (fun effect actual =>
    let (authority, attempt) := observe effect actual
    (useRedeemed receipt.result.1 authority attempt).isSome = true)

theorem redeemed_resource_preserves_gateway
    (base : CedarPooSpec.ZeroTrust.Framework E V)
    (receipt : Invocation contract prepare input)
    (observe : E → V → Authority × Attempt)
    (accepted : (strengthenResource base receipt observe).required effect actual) :
    base.required effect actual :=
  CedarPooSpec.ZeroTrust.with_requirement_preserves_framework base _ _ _ accepted

theorem redeemed_resource_rejects_revoked_use
    (base : CedarPooSpec.ZeroTrust.Framework E V)
    (receipt : Invocation contract prepare input)
    (observe : E → V → Authority × Attempt)
    (revoked : (observe effect actual).2.grant.tokenHash ∈ (observe effect actual).1.revokedTokens) :
    ¬ (strengthenResource base receipt observe).required effect actual := by
  intro accepted
  have checked := accepted.2.1.2
  change (useRedeemed receipt.result.1 (observe effect actual).1
    (observe effect actual).2).isSome = true at checked
  rw [redeemed_grant_still_obeys_revocation _ _ _ revoked] at checked
  contradiction

end CedarPooSpec.Gateway.OAuth.Code
