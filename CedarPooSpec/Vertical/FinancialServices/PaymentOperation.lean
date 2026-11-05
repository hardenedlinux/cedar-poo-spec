import Cedar.Spec.Entities

/-!
One payment instruction, with separate authorization, audit, and Host effect
boundaries. The audit policy chooses any positive number of evidence stages;
AI and human reviewers are evidence sources, not the identity of the payment.
The Host authenticates evidence and performs durable execution.
-/

namespace CedarPooSpec.Vertical.FinancialServices

open Cedar.Spec

inductive PaymentAuthorityMode where
  | direct | delegated
  deriving DecidableEq, Repr

/-- The concrete payment object. `instrument` identifies the payment rail;
    instrument-specific details and any mandate must be bound by a canonical
    Host serialization before execution. -/
structure PaymentOperation where
  authorityMode : PaymentAuthorityMode
  payerAccount : EntityUID
  origin : EntityUID
  instrument : String
  beneficiary : String
  amount : String
  asset : String
  network : String
  feeCap : String
  mandateRef : String
  /-- Optional for generic payments; AgenticAI.Commerce adapters require the exact
      merchant checkout commitment before issuing a payment request. -/
  checkoutCommitment : String := ""
  nonce : String
  proposer : String
  policyEpoch : Nat
  expiresAt : Nat
  deriving DecidableEq, Repr

inductive AuditKind where
  | model | human | rule | external
  deriving DecidableEq, Repr

inductive AuditVerdict where
  | pass | escalate | deny
  deriving DecidableEq, Repr

structure AuditRequirement where
  kind : AuditKind
  source : String
  minimum : Nat
  excludeProposer : Bool := false
  deriving DecidableEq, Repr

/-- The policy owns the number and kinds of required audit stages. -/
structure PaymentAuditPolicy where
  requirements : List AuditRequirement
  distinctHumanActors : Bool := false
  deriving DecidableEq, Repr

/-- `verified` is supplied by the Host after authenticating the source. The
    exact policy is included so evidence cannot be reused under another plan. -/
structure AuditEvidence where
  payment : PaymentOperation
  auditPolicy : PaymentAuditPolicy
  kind : AuditKind
  source : String
  actor : String
  verdict : AuditVerdict
  verified : Bool
  expiresAt : Nat
  deriving DecidableEq, Repr

/-- Authorization carries the exact audit policy seen at decision time. The
    Host supplies `verified` only after evaluating its active Cedar policy
    without errors and capturing this policy snapshot. -/
structure PaymentAuthorization where
  payment : PaymentOperation
  auditPolicy : PaymentAuditPolicy
  allowed : Bool
  verified : Bool
  deriving DecidableEq, Repr

structure PaymentState where
  policyEpoch : Nat
  auditPolicy : PaymentAuditPolicy
  now : Nat
  usedNonces : List String
  deriving DecidableEq, Repr

def PaymentOperation.wellFormed (payment : PaymentOperation) : Bool :=
  !payment.instrument.isEmpty && !payment.beneficiary.isEmpty &&
  !payment.amount.isEmpty && !payment.asset.isEmpty &&
  !payment.network.isEmpty && !payment.feeCap.isEmpty &&
  !payment.nonce.isEmpty && !payment.proposer.isEmpty &&
  (payment.authorityMode == .direct || !payment.mandateRef.isEmpty)

private def validEvidence (policy : PaymentAuditPolicy)
    (payment : PaymentOperation) (now : Nat)
    (evidence : AuditEvidence) : Bool :=
  evidence.payment == payment && decide (evidence.auditPolicy = policy) &&
  evidence.verified &&
  !evidence.source.isEmpty && !evidence.actor.isEmpty &&
  now < evidence.expiresAt && evidence.verdict == .pass

private def matchingActors (policy : PaymentAuditPolicy)
    (payment : PaymentOperation) (now : Nat)
    (evidence : List AuditEvidence) (requirement : AuditRequirement) : List String :=
  (evidence.filter fun item =>
    validEvidence policy payment now item && item.kind == requirement.kind &&
    item.source == requirement.source &&
    (!requirement.excludeProposer || item.actor != payment.proposer)).map
      AuditEvidence.actor

/-- All submitted evidence must bind this payment and exact policy, and be
    current, verified, and affirmative. A
    requirement counts distinct actors from its named source; a policy may
    additionally require distinct human actors across all human stages. -/
def PaymentAuditPolicy.accepts (policy : PaymentAuditPolicy)
    (payment : PaymentOperation) (now : Nat)
    (evidence : List AuditEvidence) : Bool :=
  !policy.requirements.isEmpty &&
  evidence.all (validEvidence policy payment now) &&
  policy.requirements.all (fun requirement =>
    !requirement.source.isEmpty && requirement.minimum > 0 &&
    (matchingActors policy payment now evidence requirement).eraseDups.length >=
      requirement.minimum) &&
  (!policy.distinctHumanActors ||
    let humans := (evidence.filter fun item => item.kind == .human).map AuditEvidence.actor
    humans.eraseDups.length == humans.length)

/-- Authorization, audit, and transaction freshness are separate checks.
    The authorization snapshot must name the current audit policy exactly. -/
def PaymentOperation.authorizedAtUse (payment : PaymentOperation)
    (authorization : PaymentAuthorization)
    (state : PaymentState) (evidence : List AuditEvidence) : Bool :=
  authorization.verified && authorization.allowed &&
  authorization.payment == payment &&
  decide (authorization.auditPolicy = state.auditPolicy) && payment.wellFormed &&
  payment.policyEpoch == state.policyEpoch && state.now < payment.expiresAt &&
  state.auditPolicy.accepts payment state.now evidence

/-- Admission adds nonce freshness to the reusable current-use assessment. A
reserved payment is reassessed at signing without unburning its nonce. -/
def PaymentOperation.admissible (payment : PaymentOperation)
    (authorization : PaymentAuthorization)
    (state : PaymentState) (evidence : List AuditEvidence) : Bool :=
  payment.authorizedAtUse authorization state evidence &&
    !(state.usedNonces.contains payment.nonce)

/-- Pure reservation. The Host must durably bind this nonce to one pending
    attempt before dispatch; this function does not execute a transfer. -/
def PaymentOperation.reserve (payment : PaymentOperation)
    (authorization : PaymentAuthorization)
    (state : PaymentState) (evidence : List AuditEvidence) : Option PaymentState :=
  if payment.admissible authorization state evidence then
    some { state with usedNonces := payment.nonce :: state.usedNonces }
  else none

theorem deniedAuthorizationCannotReserve (payment : PaymentOperation)
    (authorization : PaymentAuthorization)
    (state : PaymentState) (evidence : List AuditEvidence)
    (h : authorization.allowed = false) :
    payment.reserve authorization state evidence = none := by
  simp [PaymentOperation.reserve, PaymentOperation.admissible, PaymentOperation.authorizedAtUse, h]

theorem changedAuditPolicyCannotReserve (payment : PaymentOperation)
    (authorization : PaymentAuthorization) (state : PaymentState)
    (evidence : List AuditEvidence)
    (h : authorization.auditPolicy ≠ state.auditPolicy) :
    payment.reserve authorization state evidence = none := by
  simp [PaymentOperation.reserve, PaymentOperation.admissible, PaymentOperation.authorizedAtUse, h]

theorem reservationConsumesNonce (payment : PaymentOperation)
    (authorization : PaymentAuthorization)
    (state next : PaymentState) (evidence : List AuditEvidence)
    (h : payment.reserve authorization state evidence = some next) :
    next.usedNonces = payment.nonce :: state.usedNonces := by
  unfold PaymentOperation.reserve at h
  split at h
  · cases h
    rfl
  · simp at h

theorem reservedPaymentCannotReplay (payment : PaymentOperation)
    (authorization : PaymentAuthorization)
    (state next : PaymentState) (evidence : List AuditEvidence)
    (h : payment.reserve authorization state evidence = some next) :
    payment.reserve authorization next evidence = none := by
  have hnonce := reservationConsumesNonce payment authorization state next evidence h
  simp [PaymentOperation.reserve, PaymentOperation.admissible, PaymentOperation.authorizedAtUse, hnonce]

end CedarPooSpec.Vertical.FinancialServices
