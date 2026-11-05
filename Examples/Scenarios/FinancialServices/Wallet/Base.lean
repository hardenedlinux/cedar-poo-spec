import CedarPooSpec.Scenarios
import CedarPooSpec.Vertical.FinancialServices.PaymentSigning
import Examples.Enterprise.Agent.Payment.PaymentAudit

/-! Reusable synthetic wallet/payment signing scenario. Incident provenance and
attacker acquisition rules belong to derived reported scenarios. Existing C4 payment roots supply real Cedar decisions;
all source identities, approvals and chain observations are test fixtures. -/
namespace CedarPooSpec.WalletSigningExample
open CedarPooSpec.Vertical.FinancialServices
open PaymentSigning CedarPooSpec.Gateway.EffectProtocol CedarPooSpec.ZeroTrust
open CedarPooSpec.AgentPaymentExample CedarPooSpec.AgentDelegationExample

def payment : PaymentOperation :=
  { authorityMode := .direct, payerAccount := approvedAccount, origin := admin,
    instrument := "native-value", beneficiary := "treasury-destination",
    amount := "50.0000", asset := "ETH", network := "ethereum:1", feeCap := "1.0000",
    mandateRef := "", nonce := "withdrawal-42", proposer := "finance-bot",
    policyEpoch := 7, expiresAt := 30 }

def auditPolicy : PaymentAuditPolicy := CedarPooSpec.AgentPaymentAuditExample.auditPolicy

def auditEvidence : List AuditEvidence :=
  [(.model, "risk-v1", "risk-engine"), (.human, "risk", "risk-officer"),
    (.human, "compliance", "compliance-officer")].map fun (kind, source, actor) =>
      { payment, auditPolicy, kind, source, actor, verdict := .pass,
        verified := true, expiresAt := 25 }

def paymentState : PaymentState :=
  { policyEpoch := 7, auditPolicy, now := 10, usedNonces := [] }

/-- Only the source adapter can select this root. Request metadata cannot
replace the trusted final-use assessor or its independently configured roots. -/
def authorization (root : String) (operation : PaymentOperation) : PaymentAuthorization :=
  { payment := operation, auditPolicy,
    allowed := authorizePayment root operation.payerAccount operation.origin operation.amount,
    verified := true }

def initialLedger : PaymentLedger := { state := paymentState }

def reservedLedger : PaymentLedger :=
  { revision := 1, state := { paymentState with usedNonces := [payment.nonce] },
    attempts := [{ payment, phase := .reserved }] }

def signer : Workload := ⟨"treasury-signer", "reviewed-release-7", .paymentSigning⟩
def deployment : Workload := ⟨"wallet-devops", "malicious-container", .deployment⟩
def transaction : Transaction := Transaction.forPayment payment 42
def effect : EffectIdentity := transaction.effect payment.nonce 7 signer.subject
def review : ReviewBinding := ⟨"PaymentOrigin", "PaymentGoverned", "payment-schema",
  "reviewed-release-7", 7, "independent-review-7"⟩

def fact : FactBinding String String :=
  ⟨"treasury-workflow", "withdrawal-42", signer.subject, "payment-world-7",
    "payment-intent", transaction.payload, 7, .attested, 1, 25⟩

def envelope : Envelope := ⟨"payment-world-7", ⟨1, 0⟩, effect, review, [fact]⟩

def gateway : CedarPooSpec.Gateway.EffectProtocol.Current :=
  ⟨"payment-world-7", effect, review, ⟨fun _ => fact, fun item => decide (item = fact), 10⟩,
    ["payment-intent"], true, true, false, true, true, false⟩

def current : PaymentSigning.Current :=
  { ledger := reservedLedger, gateway, signer,
    authenticates := fun caller => decide (caller = signer ∨ caller = deployment),
    authenticatesAudit := fun item => decide (item ∈ auditEvidence),
    authorize := authorization "PaymentGoverned", chainNonce := 42 }

def request : PaymentSigning.Request :=
  { operation := payment.nonce, transaction, caller := signer,
    authorization := authorization "PaymentGoverned" payment, evidence := auditEvidence, envelope }

/-- Retained signed authority is an existing exposure, not a supported payment
operation. Local suspension and clearing submission do not establish removal. -/
def exposure : DelegationExposure :=
  { wallet := payment.payerAccount, network := payment.network,
    code := some "attacker-delegate", installedNonce := 42, clearNonce := 43 }

def clearObservation : ClearObservation :=
  { wallet := payment.payerAccount, network := payment.network, nonce := 43,
    code := none, finalized := true, verified := true }

/-- Existing C4 freeze is observed by the final-use assessor even if the caller
replays its authentic old Allow and unchanged signed envelope. -/
def frozen : PaymentSigning.Current :=
  { current with authorize := authorization "PaymentFrozen" }

def metadata : CedarPooSpec.Scenarios.Metadata :=
  { id := "wallet-native-value-signing", title := "Native-value wallet signing",
    domain := "financial-services/payment", summary := "Current authorization, exact signing terms and retained consumption",
    kind := .synthetic, limitations := ["Synthetic workflow, workload and chain readers", "No physical signer, transaction codec or deployed durability"] }

def scenario : CedarPooSpec.Scenarios.Scenario (PaymentSigning.Current × PaymentSigning.Request) :=
  (CedarPooSpec.Scenarios.create metadata (current, request)).toOption.get (by native_decide)

end CedarPooSpec.WalletSigningExample
