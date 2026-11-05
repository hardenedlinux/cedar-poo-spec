import CedarPooSpec.Vertical.FinancialServices.PaymentLedger
import CedarPooSpec.Gateway.EffectProtocol
import Lean.Data.Json

/-! A conservative native-value payment signing profile. The Host decodes the
actual signing bytes into `Transaction`, authenticates callers and current
facts, and atomically persists the returned ledger before releasing a signature.
Code delegation, contract calls and recovery signing require other profiles.
No cryptography, chain execution or complete mediation is implemented here. -/
namespace CedarPooSpec.Vertical.FinancialServices.PaymentSigning
open Cedar.Spec CedarPooSpec.Gateway CedarPooSpec.ZeroTrust
open LeanPoo.Functional.DeclarativeMetadata

inductive TransactionKind where
  | transfer | delegateCode | clearDelegation
  deriving DecidableEq, Repr

/-- Decoded signing semantics, not a caller's transaction description. Amounts
and fees retain the payment rail's representation; this is not a wei encoder. -/
structure Transaction where
  kind : TransactionKind
  payer : EntityUID
  network : String
  beneficiary : String
  amount : String
  asset : String
  feeCap : String
  nonce : Nat
  calldata : List Nat := []
  delegatedCode : Option String := none
  deriving DecidableEq, Repr

def Transaction.forPayment (payment : PaymentOperation) (nonce : Nat) : Transaction :=
  { kind := .transfer, payer := payment.payerAccount, network := payment.network,
    beneficiary := payment.beneficiary, amount := payment.amount, asset := payment.asset,
    feeCap := payment.feeCap, nonce }

/-- Structured protocol projection, not the chain signing preimage. Exact typed
equality is also required, so safety does not assume this encoding injective. -/
def Transaction.payload (tx : Transaction) : String :=
  (Lean.Json.arr #[Lean.toJson (reprStr tx.kind), Lean.toJson (toString tx.payer),
    Lean.toJson tx.network, Lean.toJson tx.beneficiary, Lean.toJson tx.amount,
    Lean.toJson tx.asset, Lean.toJson tx.feeCap, Lean.toJson tx.nonce,
    Lean.toJson tx.calldata, Lean.toJson tx.delegatedCode]).compress

def Transaction.effect (tx : Transaction) (operation : String)
    (generation : Nat) (audience : String) : EffectProtocol.EffectIdentity :=
  { operation, object := toString tx.payer, generation, payload := tx.payload,
    actionSchema := "wallet-native-transfer/v1", audience }

inductive WorkloadPurpose where
  | deployment | paymentSigning
  deriving DecidableEq, Repr

structure Workload where
  subject : String
  release : String
  purpose : WorkloadPurpose
  deriving DecidableEq, Repr

/-- Trusted current image read at use. Authentication is a Host interpretation,
never an incoming `verified` label. The ledger retains the approved payment. -/
structure Current where
  ledger : PaymentLedger
  gateway : EffectProtocol.Current
  signer : Workload
  authenticates : Workload → Bool
  authenticatesAudit : AuditEvidence → Bool
  authorize : PaymentOperation → PaymentAuthorization
  chainNonce : Nat

structure Request where
  operation : String
  transaction : Transaction
  caller : Workload
  authorization : PaymentAuthorization
  evidence : List AuditEvidence
  envelope : EffectProtocol.Envelope

def Conditions (current : Current) (request : Request) (attempt : PaymentAttempt) : Prop :=
  request.transaction = Transaction.forPayment attempt.payment current.chainNonce ∧
  request.caller = current.signer ∧
  request.caller.purpose = .paymentSigning ∧
  current.signer.subject ≠ "" ∧ current.signer.release ≠ "" ∧
  current.authenticates request.caller = true ∧
  request.evidence.all current.authenticatesAudit = true ∧
  request.authorization = current.authorize attempt.payment ∧
  attempt.payment.authorizedAtUse request.authorization current.ledger.state request.evidence = true ∧
  request.envelope.effect = request.transaction.effect request.operation
    current.gateway.effect.generation current.signer.subject ∧
  current.gateway.review.epoch = current.ledger.state.policyEpoch ∧
  EffectProtocol.accepts current.gateway request.envelope request.authorization.allowed = true

instance (current : Current) (request : Request) (attempt : PaymentAttempt) :
    Decidable (Conditions current request attempt) := by
  unfold Conditions
  infer_instance

def accepts (current : Current) (request : Request) : Bool :=
  match current.ledger.attemptFor request.operation with
  | none => false
  | some attempt => decide (Conditions current request attempt)

structure Result where
  ledger : PaymentLedger
  transaction : Transaction
  deriving DecidableEq, Repr

/-- Final-use reassessment precedes the existing reserved-to-submitted ledger
transition. A lost signing reply keeps the submitted record and original burn;
recovery must use the existing read-only reconciliation path. -/
def release (current : Current) (request : Request) : Option Result := do
  if !accepts current request then none
  let (ledger, _) ← current.ledger.dispatch request.operation
  pure { ledger, transaction := request.transaction }

theorem accepted_conditions (current : Current) (request : Request)
    (accepted : accepts current request = true) :
    ∃ attempt, current.ledger.attemptFor request.operation = some attempt ∧
      Conditions current request attempt := by
  cases found : current.ledger.attemptFor request.operation with
  | none => simp [accepts, found] at accepted
  | some attempt =>
      exact ⟨attempt, rfl, of_decide_eq_true (by simpa [accepts, found] using accepted)⟩

theorem release_requires_current_checks (current : Current) (request : Request) (result : Result)
    (released : release current request = some result) : accepts current request = true := by
  cases checked : accepts current request <;> simp [release, checked] at released ⊢

theorem release_returns_requested_transaction (current : Current) (request : Request)
    (result : Result) (released : release current request = some result) :
    result.transaction = request.transaction := by
  cases checked : accepts current request with
  | false => simp [release, checked] at released
  | true =>
    cases dispatched : current.ledger.dispatch request.operation with
    | none => simp [release, checked, dispatched] at released
    | some pair =>
        rcases pair with ⟨ledger, command⟩
        simp [release, checked, dispatched] at released
        cases released
        rfl

theorem release_binds_exact_transaction (current : Current) (request : Request) (result : Result)
    (released : release current request = some result) :
    ∃ attempt, current.ledger.attemptFor request.operation = some attempt ∧
      result.transaction = Transaction.forPayment attempt.payment current.chainNonce := by
  obtain ⟨attempt, found, checks⟩ := accepted_conditions current request
    (release_requires_current_checks current request result released)
  exact ⟨attempt, found, (release_returns_requested_transaction current request result released).trans checks.1⟩

theorem release_only_native_transfer (current : Current) (request : Request) (result : Result)
    (released : release current request = some result) :
    result.transaction.kind = .transfer ∧ result.transaction.calldata = [] ∧
      result.transaction.delegatedCode = none := by
  obtain ⟨_, _, exactTx⟩ := release_binds_exact_transaction current request result released
  rw [exactTx]
  exact ⟨rfl, rfl, rfl⟩

theorem release_retains_gateway (current : Current) (request : Request) (result : Result)
    (released : release current request = some result) :
    EffectProtocol.accepts current.gateway request.envelope request.authorization.allowed = true := by
  obtain ⟨_, _, checks⟩ := accepted_conditions current request
    (release_requires_current_checks current request result released)
  rcases checks with ⟨_, _, _, _, _, _, _, _, _, _, _, gateway⟩
  exact gateway

theorem deployment_cannot_release (current : Current) (request : Request)
    (deploy : request.caller.purpose = .deployment) : release current request = none := by
  have refused : accepts current request = false := by
    cases found : current.ledger.attemptFor request.operation <;>
      simp [accepts, found, Conditions, deploy]
  simp [release, refused]

theorem revoked_cannot_release (current : Current) (request : Request)
    (revoked : current.gateway.revoked = true) : release current request = none := by
  have refused : accepts current request = false := by
    cases found : current.ledger.attemptFor request.operation <;>
      simp [accepts, found, Conditions, EffectProtocol.accepts, revoked]
  simp [release, refused]

structure Input where
  current : Current
  request : Request

def check (input : Input) : Except String Result :=
  match release input.current input.request with
  | some result => .ok result
  | none => .error "payment signing refused"

def contract : Contract Unit Input Result where
  input := ⟨"current-payment-signing", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"reserved-exact-signing-command", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => check input = .ok result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : Input) : Except String (Result × Unit) := do
  pure (← check input, ())

theorem invocation_is_checked (receipt : Invocation contract prepare input) :
    check input = .ok receipt.result := receipt.logic

/-- Authority already installed on-chain survives local control-plane stops.
The nonce names the exact independently authorized clearing operation. -/
structure DelegationExposure where
  wallet : EntityUID
  network : String
  code : Option String
  installedNonce : Nat
  clearNonce : Nat
  withdrawalsPaused : Bool := false
  signerRevoked : Bool := false
  clearSubmitted : Bool := false
  deriving DecidableEq, Repr

structure ClearObservation where
  wallet : EntityUID
  network : String
  nonce : Nat
  code : Option String
  finalized : Bool
  verified : Bool
  deriving DecidableEq, Repr

def DelegationExposure.pause (exposure : DelegationExposure) : DelegationExposure :=
  { exposure with withdrawalsPaused := true, signerRevoked := true }

def DelegationExposure.submitClear (exposure : DelegationExposure) : DelegationExposure :=
  { exposure with clearSubmitted := true }

/-- No clearing signature is issued here. The Host authenticates the chain's
finality and canonical state, including reorg handling, before `verified`. -/
def DelegationExposure.observeClear (exposure : DelegationExposure)
    (observation : ClearObservation) : Option DelegationExposure :=
  if observation.verified && observation.finalized && exposure.clearSubmitted &&
      decide (observation.wallet = exposure.wallet ∧ observation.network = exposure.network ∧
        observation.nonce = exposure.clearNonce ∧ exposure.installedNonce < exposure.clearNonce ∧
        observation.code = none) then
    some { exposure with code := none }
  else none

theorem pause_preserves_outstanding_authority (exposure : DelegationExposure) :
    exposure.pause.code = exposure.code := rfl

theorem submission_preserves_outstanding_authority (exposure : DelegationExposure) :
    exposure.submitClear.code = exposure.code := rfl

theorem unconfirmed_clear_refused (exposure : DelegationExposure) (observation : ClearObservation)
    (unconfirmed : observation.finalized = false) : exposure.observeClear observation = none := by
  simp [DelegationExposure.observeClear, unconfirmed]

end CedarPooSpec.Vertical.FinancialServices.PaymentSigning
