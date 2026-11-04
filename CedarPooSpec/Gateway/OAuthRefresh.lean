import CedarPooSpec.Gateway.OAuthPAR

/-! Nonrotating, sender-constrained refresh families for the confidential-client
profile. The current family ledger governs refresh and resource admission. -/
namespace CedarPooSpec.Gateway.OAuth.Refresh
open LeanPoo.Functional.DeclarativeMetadata

structure RefreshDigest where
  value : String
  deriving DecidableEq

structure FamilyKey where
  issuer : String
  refreshDigest : RefreshDigest
  deriving DecidableEq

structure Family where
  key : FamilyKey
  registration : PAR.Registration
  original : Grant
  expiresAt : Nat
  deriving DecidableEq

/-- Access digests stay associated with their original family after revocation. -/
structure Access where
  family : FamilyKey
  grant : Grant
  deriving DecidableEq

structure Ledger where
  families : List Family := []
  access : List Access := []
  revoked : List FamilyKey := []
  deriving DecidableEq

def Ledger.family (ledger : Ledger) (key : FamilyKey) : Option Family :=
  match ledger.families.filter (fun family => decide (family.key = key)) with
  | [family] => some family
  | _ => none

def Ledger.accessEntry (ledger : Ledger) (digest : String) : Option Access :=
  match ledger.access.filter (fun entry => entry.grant.tokenHash == digest) with
  | [entry] => some entry
  | _ => none

def Ledger.unissued (ledger : Ledger) (digest : String) : Bool :=
  !digest.isEmpty && !(ledger.access.any fun entry => entry.grant.tokenHash == digest)

structure Enrollment (input : PAR.RedemptionInput authorization) where
  receipt : Invocation (PAR.redemptionContract authorization) PAR.prepareRedemption input
  ledger : Ledger
  refreshDigest : RefreshDigest
  now : Nat
  expiresAt : Nat

def enroll (input : Enrollment redemption) : Option Ledger :=
  let grant := input.receipt.result.1
  let key : FamilyKey := ⟨grant.identity.issuer, input.refreshDigest⟩
  if !input.refreshDigest.value.isEmpty && input.now < input.expiresAt &&
    input.ledger.unissued grant.tokenHash &&
    !(input.ledger.families.any fun family => decide (family.key = key)) &&
    decide (key ∉ input.ledger.revoked) then
    let family : Family := ⟨key, redemption.receipt.result.pushed.registration, grant, input.expiresAt⟩
    some { input.ledger with
      families := family :: input.ledger.families
      access := ⟨key, grant⟩ :: input.ledger.access }
  else none

def enrollmentContract (redemption : PAR.RedemptionInput authorization) :
    Contract Unit (Enrollment redemption) Ledger where
  input := ⟨"PAR-redemption-and-fresh-refresh-digest", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"initial-access-grant-and-refresh-family", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => enroll input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareEnrollment (input : Enrollment redemption) : Except String (Ledger × Unit) :=
  match enroll input with
  | some result => .ok (result, ())
  | none => .error "OAuth refresh enrollment refused"

theorem enrollment_retains_sender
    (receipt : Invocation (enrollmentContract redemption) prepareEnrollment input) :
    let original := input.receipt.result.1
    let key : FamilyKey := ⟨original.identity.issuer, input.refreshDigest⟩
    receipt.result.families =
      ⟨key, redemption.receipt.result.pushed.registration, original, input.expiresAt⟩ ::
        input.ledger.families ∧
    receipt.result.access = ⟨key, original⟩ :: input.ledger.access ∧
    receipt.result.revoked = input.ledger.revoked := by
  have accepted := receipt.logic
  change enroll input = some receipt.result at accepted
  simp only [enroll] at accepted
  split at accepted
  · rw [← Option.some.inj accepted]
    exact ⟨rfl, rfl, rfl⟩
  · contradiction

structure RefreshRequest where
  refreshDigest : RefreshDigest
  sender : PAR.TokenSender

structure RefreshInput where
  ledger : Ledger
  verified : PAR.VerifiedClient RefreshRequest
  next : Grant
  now : Nat

def RefreshInput.key (input : RefreshInput) : FamilyKey :=
  ⟨input.verified.issuer, input.verified.request.refreshDigest⟩

def Family.permits (family : Family) (grant : Grant) : Bool :=
  decide (grant.identity = family.original.identity) &&
    decide (grant.confirmation = family.original.confirmation) &&
    grant.audiences.all family.original.audiences.contains &&
    grant.scopes.all family.original.scopes.contains

def refresh (input : RefreshInput) : Option (Grant × Ledger) := do
  let family ← input.ledger.family input.key
  if input.key ∉ input.ledger.revoked ∧ input.now < family.expiresAt ∧
      input.verified.matches family.registration = true ∧
      input.verified.request.sender.matches input.verified.credential family.original.confirmation = true ∧
      family.permits input.next = true ∧ input.ledger.unissued input.next.tokenHash = true ∧
      input.next.notBefore ≤ input.now ∧ input.now < input.next.expiresAt then
    some (input.next, { input.ledger with access := ⟨input.key, input.next⟩ :: input.ledger.access })
  else none

def contract : Contract Unit RefreshInput (Grant × Ledger) where
  input := ⟨"current-refresh-family-and-verified-sender", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"issued-access-grant-and-family-ledger", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => refresh input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : RefreshInput) : Except String ((Grant × Ledger) × Unit) :=
  match refresh input with
  | some result => .ok (result, ())
  | none => .error "OAuth refresh refused"

theorem refresh_preserves_sender {family : Family}
    (found : input.ledger.family input.key = some family)
    (receipt : Invocation contract prepare input) :
    receipt.result.1.confirmation = family.original.confirmation ∧
    input.verified.request.sender.matches input.verified.credential family.original.confirmation = true ∧
    receipt.result.2.families = input.ledger.families ∧
    receipt.result.2.revoked = input.ledger.revoked ∧
    receipt.result.2.access = ⟨input.key, receipt.result.1⟩ :: input.ledger.access := by
  have accepted := receipt.logic
  change refresh input = some receipt.result at accepted
  simp only [refresh, found, bind, Option.bind] at accepted
  split at accepted
  · rename_i valid
    obtain ⟨_, _, _, sender, permitted, _⟩ := valid
    have binding : input.next.confirmation = family.original.confirmation := by
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp permitted).1).1).2
    rw [← Option.some.inj accepted]
    exact ⟨binding, sender, rfl, rfl, rfl⟩
  · contradiction

theorem wrong_sender_refused {family : Family}
    (found : input.ledger.family input.key = some family)
    (wrong : input.verified.request.sender.matches input.verified.credential
      family.original.confirmation = false) : refresh input = none := by
  simp [refresh, found, wrong]

theorem revoked_refresh_refused (input : RefreshInput) (revoked : input.key ∈ input.ledger.revoked) :
    refresh input = none := by
  cases found : input.ledger.family input.key <;> simp [refresh, found, revoked]

structure RevocationInput where
  ledger : Ledger
  verified : PAR.VerifiedClient RefreshDigest

def RevocationInput.key (input : RevocationInput) : FamilyKey :=
  ⟨input.verified.issuer, input.verified.request⟩

/-- The authenticated client can revoke a family even after losing its sender key. -/
def revoke (input : RevocationInput) : Option Ledger := do
  let family ← input.ledger.family input.key
  if input.verified.matches family.registration then
    if input.key ∈ input.ledger.revoked then some input.ledger
    else some { input.ledger with revoked := input.key :: input.ledger.revoked }
  else none

def revokeContract : Contract Unit RevocationInput Ledger where
  input := ⟨"authenticated-refresh-family-revocation", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"revoked-family-ledger", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => revoke input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareRevoke (input : RevocationInput) : Except String (Ledger × Unit) :=
  match revoke input with
  | some result => .ok (result, ())
  | none => .error "OAuth family revocation refused"

theorem revocation_retains_lineage (receipt : Invocation revokeContract prepareRevoke input) :
    input.key ∈ receipt.result.revoked ∧
    receipt.result.access = input.ledger.access ∧ receipt.result.families = input.ledger.families := by
  have accepted := receipt.logic
  change revoke input = some receipt.result at accepted
  cases found : input.ledger.family input.key with
  | none => simp [revoke, found] at accepted
  | some family =>
    simp only [revoke, found, bind, Option.bind] at accepted
    split at accepted
    · split at accepted
      · rename_i already
        rw [← Option.some.inj accepted]
        exact ⟨already, rfl, rfl⟩
      · rw [← Option.some.inj accepted]
        exact ⟨by simp, rfl, rfl⟩
    · contradiction

def useAccess (ledger : Ledger) (authority : Authority) (attempt : Attempt) : Option Authority := do
  let entry ← ledger.accessEntry attempt.grant.tokenHash
  if entry.grant = attempt.grant ∧ entry.family ∉ ledger.revoked ∧
      (ledger.family entry.family).isSome = true then
    authority.commit attempt
  else none

theorem revoked_access_refused (ledger : Ledger)
    (linked : ledger.accessEntry attempt.grant.tokenHash = some entry)
    (revoked : entry.family ∈ ledger.revoked) : useAccess ledger authority attempt = none := by
  simp [useAccess, linked, revoked]

/-- Family status is checked on the deciding view alongside the current sender,
per-token authority and the original Zero Trust requirements. -/
def strengthenResource (base : CedarPooSpec.ZeroTrust.Framework E V)
    (observe : E → V → Ledger × Authority × Attempt) :=
  base.withRequirement (fun effect actual =>
    let (ledger, authority, attempt) := observe effect actual
    (useAccess ledger authority attempt).isSome = true)

theorem revocation_blocks_linked_access
    (receipt : Invocation revokeContract prepareRevoke input)
    (linked : input.ledger.accessEntry attempt.grant.tokenHash = some entry)
    (family : entry.family = input.key) :
    useAccess receipt.result authority attempt = none := by
  have ⟨revoked, access, _⟩ := revocation_retains_lineage receipt
  have found : receipt.result.accessEntry attempt.grant.tokenHash = some entry := by
    simpa only [Ledger.accessEntry, access] using linked
  exact revoked_access_refused _ found (family.symm ▸ revoked)

theorem revoked_family_blocks_resource_contract
    (base : CedarPooSpec.ZeroTrust.Framework E V)
    (observe : E → V → Ledger × Authority × Attempt)
    (receipt : Invocation revokeContract prepareRevoke input)
    (current : (observe effect actual).1 = receipt.result)
    (linked : input.ledger.accessEntry (observe effect actual).2.2.grant.tokenHash = some entry)
    (family : entry.family = input.key) :
    ¬ (strengthenResource base observe).required effect actual := by
  intro accepted
  have checked := accepted.2.1.2
  change (useAccess (observe effect actual).1 (observe effect actual).2.1
    (observe effect actual).2.2).isSome = true at checked
  rw [current, revocation_blocks_linked_access receipt linked family] at checked
  contradiction

theorem revocation_blocks_refresh
    (receipt : Invocation revokeContract prepareRevoke input)
    (retry : RefreshInput) (same : retry.key = input.key) (current : retry.ledger = receipt.result) :
    refresh retry = none := by
  apply revoked_refresh_refused
  rw [same, current]
  exact (revocation_retains_lineage receipt).1

end CedarPooSpec.Gateway.OAuth.Refresh
