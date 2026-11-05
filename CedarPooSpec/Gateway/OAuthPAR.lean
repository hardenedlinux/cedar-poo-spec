import CedarPooSpec.Gateway.OAuthCode

/-! Pushed authorization for confidential clients. The adapter authenticates
the request at the selected issuer before constructing a VerifiedClient. -/
namespace CedarPooSpec.Gateway.OAuth.PAR
open LeanPoo.Functional.DeclarativeMetadata

inductive Credential where
  | mtls (thumbprint : String)
  | privateKeyJwt (thumbprint : String)
  deriving DecidableEq

def Credential.thumbprint : Credential → String
  | .mtls value | .privateKeyJwt value => value

structure Registration where
  issuer : String
  client : String
  credential : Credential
  redirects : List String
  scopes : List String
  deriving DecidableEq

/-- Trusted endpoint observation carrying the very request that was authenticated.
The credential is observed by the verifier. Redirect policy comes from registration. -/
structure VerifiedClient (Payload : Type) where
  issuer : String
  client : String
  credential : Credential
  request : Payload

def VerifiedClient.matches (verified : VerifiedClient Payload) (registration : Registration) : Bool :=
  verified.issuer == registration.issuer && verified.client == registration.client &&
    decide (verified.credential = registration.credential) &&
    !registration.credential.thumbprint.isEmpty

inductive DPoPEndpoint where
  | par
  | token

/-- Thumbprint of a DPoP proof verified for the actual endpoint and request.
The adapter checks the signature, target, time, nonce and applicable replay policy. -/
structure VerifiedDPoP (endpoint : DPoPEndpoint) where
  thumbprint : String
  deriving DecidableEq

/-- Sender constraint requested over the authenticated PAR back channel.
A DPoP proof header, a body dpop_jkt, or both can supply the key. -/
inductive ParSender where
  | dpop (jkt : Option String) (proof : Option (VerifiedDPoP .par))
  | mtls
  deriving DecidableEq

def ParSender.key (jkt : Option String) (proof : Option (VerifiedDPoP .par)) : Option String := do
  let key ← jkt.or (proof.map VerifiedDPoP.thumbprint)
  if !key.isEmpty && proof.all (fun observed => observed.thumbprint == key) then some key else none

def ParSender.valid : ParSender → Bool
  | .dpop jkt proof => (ParSender.key jkt proof).isSome
  | .mtls => true

def ParSender.permits : ParSender → Confirmation → Bool
  | .dpop jkt proof, .dpop key => ParSender.key jkt proof == some key
  | .mtls, .mtls certificate => !certificate.isEmpty
  | _, _ => false

structure Request where
  session : Code.Session
  audiences : List String
  scopes : List String
  sender : ParSender
  deriving DecidableEq

structure Pushed where
  uri : String
  request : Request
  registration : Registration
  expiresAt : Nat
  deriving DecidableEq

structure Ledger where
  pushed : List Pushed := []
  consumed : List (String × String) := []
  codes : Code.Ledger := { issued := [] }
  deriving DecidableEq

structure PushInput where
  ledger : Ledger
  registration : Registration
  verified : VerifiedClient Request
  uri : String
  now : Nat
  expiresAt : Nat

def push (input : PushInput) : Option Ledger :=
  let request := input.verified.request
  let session := request.session
  if input.verified.matches input.registration &&
    !session.issuer.isEmpty && !session.client.isEmpty && !session.redirect.isEmpty &&
    !session.state.isEmpty && !session.browser.isEmpty && !session.s256.isEmpty &&
    session.issuer == input.registration.issuer && session.client == input.registration.client &&
    input.registration.redirects.contains session.redirect &&
    request.scopes.all input.registration.scopes.contains && request.sender.valid && !input.uri.isEmpty &&
    input.now < input.expiresAt && input.expiresAt < input.now + 600 &&
    !(input.ledger.pushed.any fun item => item.registration.issuer == session.issuer &&
      item.uri == input.uri) then
    some { input.ledger with
      pushed := ⟨input.uri, request, input.registration, input.expiresAt⟩ :: input.ledger.pushed }
  else none

def pushContract : Contract Unit PushInput Ledger where
  input := ⟨"registered-client-and-authenticated-PAR", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"issuer-scoped-pushed-request", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => push input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def preparePush (input : PushInput) : Except String (Ledger × Unit) :=
  match push input with
  | some result => .ok (result, ())
  | none => .error "OAuth PAR refused"

theorem push_retains_request (receipt : Invocation pushContract preparePush input) :
    receipt.result.pushed =
      ⟨input.uri, input.verified.request, input.registration, input.expiresAt⟩ :: input.ledger.pushed ∧
    receipt.result.consumed = input.ledger.consumed ∧ receipt.result.codes = input.ledger.codes := by
  have accepted := receipt.logic
  change push input = some receipt.result at accepted
  simp only [push] at accepted
  split at accepted
  · rw [← Option.some.inj accepted]
    exact ⟨rfl, rfl, rfl⟩
  · contradiction

/-- The trusted client retains its expected handle and pending session.
The front-channel parser reports extra parameters, including duplicates. -/
structure AuthorizationInput where
  ledger : Ledger
  expectedUri : String
  session : Code.Session
  uri : String
  client : String
  hasExtraParameters : Bool
  now : Nat
  code : String
  codeExpiresAt : Nat
  grant : Grant

def AuthorizationInput.key (input : AuthorizationInput) := (input.session.issuer, input.uri)

def Ledger.lookup (ledger : Ledger) (issuer uri : String) : Option Pushed :=
  match ledger.pushed.filter (fun item => item.registration.issuer == issuer && item.uri == uri) with
  | [item] => some item
  | _ => none

def Request.permits (request : Request) (grant : Grant) : Bool :=
  grant.identity.issuer == request.session.issuer && grant.identity.client == request.session.client &&
    grant.audiences.all request.audiences.contains && grant.scopes.all request.scopes.contains &&
    request.sender.permits grant.confirmation

structure Authorized where
  pushed : Pushed
  issued : Code.Issued
  ledger : Ledger
  deriving DecidableEq

def authorize (input : AuthorizationInput) : Option Authorized := do
  let pushed ← input.ledger.lookup input.session.issuer input.uri
  if input.uri = input.expectedUri ∧ input.client = input.session.client ∧
      input.hasExtraParameters = false ∧ pushed.request.session = input.session ∧
      pushed.registration.issuer = input.session.issuer ∧
      pushed.registration.client = input.session.client ∧
      input.key ∉ input.ledger.consumed ∧ input.now < pushed.expiresAt ∧
      pushed.request.permits input.grant = true ∧ input.code ≠ "" ∧
      input.now < input.codeExpiresAt ∧ input.codeExpiresAt ≤ input.now + 60 ∧
      (input.ledger.codes.issued.any fun item =>
        item.session.issuer == input.session.issuer && item.code == input.code) = false ∧
      (input.session.issuer, input.code) ∉ input.ledger.codes.spent then
    let issued : Code.Issued := ⟨input.code, pushed.request.session, input.grant, input.codeExpiresAt⟩
    some ⟨pushed, issued, { input.ledger with
      consumed := input.key :: input.ledger.consumed
      codes := { input.ledger.codes with issued := issued :: input.ledger.codes.issued } }⟩
  else none

def authorizationContract : Contract Unit AuthorizationInput Authorized where
  input := ⟨"trusted-pending-session-and-front-channel-reference", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"consumed-PAR-and-bound-code", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => authorize input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareAuthorization (input : AuthorizationInput) : Except String (Authorized × Unit) :=
  match authorize input with
  | some result => .ok (result, ())
  | none => .error "OAuth pushed authorization refused"

theorem authorization_retains_binding
    (accepted : authorize input = some result) :
    input.ledger.lookup input.session.issuer input.uri = some result.pushed ∧
    input.uri = input.expectedUri ∧ input.client = input.session.client ∧
    input.hasExtraParameters = false ∧ result.pushed.request.session = input.session ∧
    result.pushed.registration.issuer = input.session.issuer ∧
    result.pushed.registration.client = input.session.client ∧
    result.issued.session = input.session ∧
    result.pushed.request.permits result.issued.grant = true ∧ input.key ∈ result.ledger.consumed ∧
    input.now < result.issued.expiresAt ∧ result.issued.expiresAt ≤ input.now + 60 := by
  cases found : input.ledger.lookup input.session.issuer input.uri with
  | none => simp [authorize, found] at accepted
  | some pushed =>
    simp only [authorize, found, bind, Option.bind] at accepted
    split at accepted
    · rename_i valid
      cases accepted
      obtain ⟨uri, client, extras, session, issuer, owner, _, _, grant, _, unexpired, lifetime, _⟩ := valid
      exact ⟨rfl, uri, client, extras, session, issuer, owner, session, grant, by simp, unexpired, lifetime⟩
    · contradiction

theorem consumed_reference_refused (input : AuthorizationInput)
    (consumed : input.key ∈ input.ledger.consumed) : authorize input = none := by
  cases found : input.ledger.lookup input.session.issuer input.uri <;>
    simp [authorize, found, consumed]

/-- Sender evidence from the actual token request. For mTLS, the peer
certificate comes from the token endpoint TLS connection. -/
inductive TokenSender where
  | dpop (proof : VerifiedDPoP .token)
  | mtls (peer : String)

def TokenSender.matches (sender : TokenSender) (client : Credential) (confirmation : Confirmation) : Bool :=
  match sender, confirmation with
  | .dpop proof, .dpop key => !key.isEmpty && proof.thumbprint == key
  | .mtls peer, .mtls certificate =>
    !certificate.isEmpty && peer == certificate &&
      (match client with
       | .mtls authenticated => peer == authenticated
       | .privateKeyJwt _ => true)
  | _, _ => false

structure TokenRequest where
  redemption : Code.Request
  sender : TokenSender

structure RedemptionInput (authorization : AuthorizationInput) where
  receipt : Invocation authorizationContract prepareAuthorization authorization
  ledger : Code.Ledger
  verified : VerifiedClient TokenRequest
  now : Nat

def RedemptionInput.codeInput (input : RedemptionInput authorization) : Code.Input :=
  ⟨input.ledger, input.receipt.result.issued.session, input.verified.request.redemption, input.now⟩

def redeem (input : RedemptionInput authorization) : Option (Grant × Code.Ledger) :=
  let authorized := input.receipt.result
  if input.verified.matches authorized.pushed.registration = true ∧
    input.verified.request.sender.matches input.verified.credential authorized.issued.grant.confirmation = true ∧
    input.ledger.lookup authorized.issued.session input.verified.request.redemption.code = some authorized.issued then
    Code.redeem input.codeInput
  else none

def redemptionContract (authorization : AuthorizationInput) :
    Contract Unit (RedemptionInput authorization) (Grant × Code.Ledger) where
  input := ⟨"authenticated-token-request-and-authorization-receipt", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"redeemed-PAR-grant-and-spent-code", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => redeem input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareRedemption (input : RedemptionInput authorization) :
    Except String ((Grant × Code.Ledger) × Unit) :=
  match redeem input with
  | some result => .ok (result, ())
  | none => .error "OAuth pushed code redemption refused"

theorem redemption_retains_binding
    (accepted : redeem input = some result) :
    input.verified.matches input.receipt.result.pushed.registration = true ∧
    input.verified.request.sender.matches input.verified.credential
      input.receipt.result.issued.grant.confirmation = true ∧
    input.ledger.lookup input.receipt.result.issued.session input.verified.request.redemption.code =
      some input.receipt.result.issued ∧ Code.redeem input.codeInput = some result := by
  simp only [redeem] at accepted
  split at accepted
  · rename_i valid
    exact ⟨valid.1, valid.2.1, valid.2.2, accepted⟩
  · contradiction

def codeReceipt (receipt : Invocation (redemptionContract authorization) prepareRedemption input) :
    Invocation Code.contract Code.prepare input.codeInput :=
  have checked := (redemption_retains_binding receipt.logic).2.2.2
  ⟨receipt.result, (), by simp [Code.prepare, checked], trivial, trivial, checked⟩

theorem redeemed_grant_respects_pushed_request
    (receipt : Invocation (redemptionContract authorization) prepareRedemption input) :
    receipt.result.1 = input.receipt.result.issued.grant ∧
    input.receipt.result.pushed.request.permits receipt.result.1 = true := by
  have ⟨_, _, selected, _⟩ := redemption_retains_binding receipt.logic
  obtain ⟨item, found, _, returned, _⟩ := Code.redemption_retains_binding (codeReceipt receipt)
  change input.ledger.lookup input.receipt.result.issued.session input.verified.request.redemption.code =
    some item at found
  have same := Option.some.inj (found.symm.trans selected)
  have grant : receipt.result.1 = input.receipt.result.issued.grant := by
    simpa only [codeReceipt, same] using returned
  obtain ⟨_, _, _, _, _, _, _, _, permitted, _⟩ :=
    authorization_retains_binding input.receipt.logic
  exact ⟨grant, grant.symm ▸ permitted⟩

/-- A DPoP token uses exactly the PAR key, and the token endpoint checked
possession of that key before the code was spent. -/
theorem redeemed_dpop_key
    (receipt : Invocation (redemptionContract authorization) prepareRedemption input)
    (pushed : input.receipt.result.pushed.request.sender = .dpop jkt parProof)
    (key : ParSender.key jkt parProof = some thumbprint) :
    receipt.result.1.confirmation = .dpop thumbprint ∧
      ∃ proof, input.verified.request.sender = .dpop proof ∧ proof.thumbprint = thumbprint := by
  have ⟨grant, permitted⟩ := redeemed_grant_respects_pushed_request receipt
  have ⟨_, observed, _, _⟩ := redemption_retains_binding receipt.logic
  have bound : input.receipt.result.pushed.request.sender.permits receipt.result.1.confirmation = true :=
    (Bool.and_eq_true_iff.mp permitted).2
  cases confirmation : receipt.result.1.confirmation with
  | mtls certificate => simp [pushed, ParSender.permits, confirmation] at bound
  | dpop actual =>
    have same : thumbprint = actual := by simpa [pushed, ParSender.permits, confirmation, key] using bound
    subst actual
    rw [← grant, confirmation] at observed
    cases h : input.verified.request.sender with
    | mtls peer => simp [h, TokenSender.matches] at observed
    | dpop proof =>
      have matchKey : proof.thumbprint = thumbprint := by
        simpa [h, TokenSender.matches] using (Bool.and_eq_true_iff.mp
          (show !thumbprint.isEmpty && (proof.thumbprint == thumbprint) = true by
            simpa [h, TokenSender.matches] using observed)).2
      exact ⟨rfl, proof, rfl, matchKey⟩

/-- The token certificate is observed on the token connection. When that
connection also authenticates the client, both observations must agree. -/
theorem redeemed_mtls_certificate
    (receipt : Invocation (redemptionContract authorization) prepareRedemption input)
    (confirmation : receipt.result.1.confirmation = .mtls certificate) :
    input.verified.request.sender = .mtls certificate ∧
      ∀ authenticated, input.verified.credential = .mtls authenticated → certificate = authenticated := by
  have ⟨grant, _⟩ := redeemed_grant_respects_pushed_request receipt
  have ⟨_, observed, _, _⟩ := redemption_retains_binding receipt.logic
  rw [← grant, confirmation] at observed
  cases h : input.verified.request.sender with
  | dpop proof => simp [h, TokenSender.matches] at observed
  | mtls peer =>
    simp only [h, TokenSender.matches] at observed
    have checked := Bool.and_eq_true_iff.mp observed
    have same : peer = certificate := by
      simpa using (Bool.and_eq_true_iff.mp checked.1).2
    subst peer
    refine ⟨rfl, ?_⟩
    intro authenticated auth
    simpa [auth] using checked.2

theorem wrong_token_sender_refused (input : RedemptionInput authorization)
    (wrong : input.verified.request.sender.matches input.verified.credential
      input.receipt.result.issued.grant.confirmation = false) : redeem input = none := by
  simp [redeem, wrong]

/-- Carry the checked redemption into the existing current-use Contract. -/
def strengthenResource
    (base : CedarPooSpec.ZeroTrust.Framework E V)
    (receipt : Invocation (redemptionContract authorization) prepareRedemption input)
    (observe : E → V → Authority × Attempt) :=
  Code.strengthenResource base (codeReceipt receipt) observe

theorem resource_requires_redeemed_sender
    (base : CedarPooSpec.ZeroTrust.Framework E V)
    (receipt : Invocation (redemptionContract authorization) prepareRedemption input)
    (observe : E → V → Authority × Attempt)
    (accepted : (strengthenResource base receipt observe).required effect actual) :
    let (authority, attempt) := observe effect actual
    attempt.grant = receipt.result.1 ∧ (authority.observe attempt).senderBound := by
  have checked := accepted.2.1.2
  change (Code.useRedeemed receipt.result.1 (observe effect actual).1
    (observe effect actual).2).isSome = true at checked
  simp only [Code.useRedeemed] at checked
  split at checked
  · rename_i grant
    simp only [Authority.commit] at checked
    split at checked
    · rename_i bound
      unfold CurrentUse.bound at bound
      obtain ⟨_, _, _, _, _, _, _, _, _, sender⟩ := bound
      exact ⟨grant, sender⟩
    · contradiction
  · contradiction

/-- Actual resource evidence must identify the sender carried by the
redeemed grant. In particular, a DPoP key selected in PAR is checked here. -/
theorem resource_matches_confirmation
    (base : CedarPooSpec.ZeroTrust.Framework E V)
    (receipt : Invocation (redemptionContract authorization) prepareRedemption input)
    (observe : E → V → Authority × Attempt)
    (accepted : (strengthenResource base receipt observe).required effect actual) :
    match (observe effect actual).2.sender with
    | .dpop proof => receipt.result.1.confirmation = .dpop proof.thumbprint
    | .mtls peer => receipt.result.1.confirmation = .mtls peer := by
  have ⟨grant, bound⟩ := resource_requires_redeemed_sender base receipt observe accepted
  cases sender : (observe effect actual).2.sender <;> cases confirmation : receipt.result.1.confirmation <;>
    simp [Authority.observe, CurrentUse.senderBound, sender, grant, confirmation] at bound ⊢
  · obtain ⟨_, _, _, _, _, key, _⟩ := bound
    exact key.symm
  · exact bound.2.symm

theorem resource_preserves_par_dpop_key
    (base : CedarPooSpec.ZeroTrust.Framework E V)
    (receipt : Invocation (redemptionContract authorization) prepareRedemption input)
    (observe : E → V → Authority × Attempt)
    (pushed : input.receipt.result.pushed.request.sender = .dpop jkt parProof)
    (key : ParSender.key jkt parProof = some thumbprint)
    (accepted : (strengthenResource base receipt observe).required effect actual) :
    ∃ proof, (observe effect actual).2.sender = .dpop proof ∧ proof.thumbprint = thumbprint := by
  have confirmation := (redeemed_dpop_key receipt pushed key).1
  have sender := resource_matches_confirmation base receipt observe accepted
  cases observed : (observe effect actual).2.sender with
  | dpop proof =>
    rw [observed, confirmation] at sender
    exact ⟨proof, rfl, (Confirmation.dpop.inj sender).symm⟩
  | mtls peer => simp [observed, confirmation] at sender

theorem authorized_reference_cannot_be_reused
    (receipt : Invocation authorizationContract prepareAuthorization input)
    (retry : AuthorizationInput) (sameKey : retry.key = input.key)
    (current : retry.ledger = receipt.result.ledger) : authorize retry = none := by
  apply consumed_reference_refused
  rw [sameKey, current]
  obtain ⟨_, _, _, _, _, _, _, _, _, consumed, _⟩ := authorization_retains_binding receipt.logic
  exact consumed

theorem redeemed_code_cannot_be_reused
    (receipt : Invocation (redemptionContract authorization) prepareRedemption input)
    (retry : RedemptionInput authorization) (sameKey : retry.codeInput.key = input.codeInput.key)
    (current : retry.ledger = receipt.result.2) : redeem retry = none := by
  have refused := Code.redeemed_code_cannot_be_reused (codeReceipt receipt) retry.codeInput sameKey current
  simp only [redeem]
  split
  · exact refused
  · rfl

theorem resource_rejects_revoked_grant
    (base : CedarPooSpec.ZeroTrust.Framework E V)
    (receipt : Invocation (redemptionContract authorization) prepareRedemption input)
    (observe : E → V → Authority × Attempt)
    (revoked : (observe effect actual).2.grant.tokenHash ∈ (observe effect actual).1.revokedTokens) :
    ¬ (strengthenResource base receipt observe).required effect actual :=
  Code.redeemed_resource_rejects_revoked_use base (codeReceipt receipt) observe revoked

end CedarPooSpec.Gateway.OAuth.PAR
