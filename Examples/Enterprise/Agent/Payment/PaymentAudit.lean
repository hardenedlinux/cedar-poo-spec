import CedarPooSpec.Vertical.FinancialServices.PaymentLedger
import Examples.Enterprise.Agent.Payment.AgentPayment

/-! Example adapter: bind a public payment operation to this Cedar policy. -/

namespace CedarPooSpec.AgentPaymentAuditExample

open CedarPooSpec.Vertical.FinancialServices
open CedarPooSpec.AgentPaymentExample

/-- This example requires three audit stages. Other payment instruments and risk
    levels may use a different policy without changing `PaymentOperation`. -/
def auditPolicy : PaymentAuditPolicy :=
  { requirements := [
      { kind := .model, source := "risk-v1", minimum := 1 },
      { kind := .human, source := "risk", minimum := 1,
        excludeProposer := true },
      { kind := .human, source := "compliance", minimum := 1,
        excludeProposer := true }],
    distinctHumanActors := true }

/-- This example uses Cedar's fixed four-place decimal representation for
    amounts and fee caps. Other payment rails may choose another profile. -/
def canonicalCedarDecimal (text : String) : Option Cedar.Spec.Ext.Decimal := do
  let value ← Cedar.Spec.Ext.Decimal.decimal text
  if toString value = text then some value else none

theorem canonicalCedarDecimalKeepsSpelling (text : String)
    (value : Cedar.Spec.Ext.Decimal)
    (h : canonicalCedarDecimal text = some value) :
    toString value = text := by
  simp only [canonicalCedarDecimal] at h
  cases hparse : Cedar.Spec.Ext.Decimal.decimal text with
  | none => simp [hparse] at h
  | some parsed =>
    simp [hparse] at h
    rcases h with ⟨hcanonical, rfl⟩
    exact hcanonical

/-- Synthetic Host scope for this one bank-rail example. `verified` is a Host
    assertion; no mandate signature or merchant registry is checked here. -/
structure PaymentExecutionProfile where
  authorityMode : PaymentAuthorityMode
  instrument : String
  beneficiary : String
  asset : String
  network : String
  mandateRef : String
  maxFeeCap : String
  verified : Bool

def executionProfile : PaymentExecutionProfile :=
  { authorityMode := .delegated, instrument := "bank-transfer",
    beneficiary := "merchant-42", asset := "USD", network := "bank-rail",
    mandateRef := "delegation-77", maxFeeCap := "1.0000", verified := true }

def PaymentExecutionProfile.allows (profile : PaymentExecutionProfile)
    (payment : PaymentOperation) : Bool :=
  profile.verified && payment.authorityMode == profile.authorityMode &&
  payment.instrument == profile.instrument &&
  payment.beneficiary == profile.beneficiary &&
  payment.asset == profile.asset && payment.network == profile.network &&
  payment.mandateRef == profile.mandateRef &&
  match canonicalCedarDecimal payment.feeCap,
      canonicalCedarDecimal profile.maxFeeCap with
  | some feeCap, some maximum =>
      feeCap.toInt >= 0 && feeCap.toInt <= maximum.toInt
  | _, _ => false

def cedarAllowed
     (payment : PaymentOperation)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Bool :=
  match canonicalCedarDecimal payment.amount with
  | none => false
  | some _ =>
    (authorizePayment (programContext := programContext)) "PaymentGoverned" payment.payerAccount payment.origin
      payment.amount

/-- Cedar handles account, origin, and amount; the synthetic Host profile binds
    the other terms before this example records a payment authorization. -/
def exampleAllowed
     (payment : PaymentOperation)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Bool :=
  executionProfile.allows payment && (cedarAllowed (programContext := programContext)) payment

def cedarAuthorization
     (payment : PaymentOperation)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : PaymentAuthorization :=
  { payment, auditPolicy, allowed := (exampleAllowed (programContext := programContext)) payment, verified := true }

def reserveWithCedar
     (payment : PaymentOperation) (state : PaymentState)
    (evidence : List AuditEvidence)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Option PaymentState :=
  payment.reserve ((cedarAuthorization (programContext := programContext)) payment) state evidence

/-- The Host-facing pure path keeps this example's Cedar decision and numeric
    checks attached to the ledger's atomic preparation transition. -/
def prepareLedgerWithCedar
     (ledger : PaymentLedger) (payment : PaymentOperation)
    (evidence : List AuditEvidence)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Option PaymentLedger :=
  ledger.prepare payment ((cedarAuthorization (programContext := programContext)) payment) evidence

/-- The bank-rail profile checks a reported fee against the approved cap.
    Exact effect-term matching remains in `PaymentAttempt.observe`. -/
def settlementFeeWithinCap (payment : PaymentOperation)
    (details : SettlementDetails) : Bool :=
  match canonicalCedarDecimal payment.feeCap,
      canonicalCedarDecimal details.chargedFee with
  | some cap, some charged => charged.toInt >= 0 && charged.toInt <= cap.toInt
  | _, _ => false

def reconcileLedgerWithFeeCap (ledger : PaymentLedger)
    (evidence : ProcessorEvidence) : Option PaymentLedger :=
  match evidence.outcome, evidence.settlement with
  | .settled, some details =>
      if settlementFeeWithinCap evidence.payment details then
        ledger.reconcile evidence
      else none
  | .settled, none => none
  | _, _ => ledger.reconcile evidence

end CedarPooSpec.AgentPaymentAuditExample
