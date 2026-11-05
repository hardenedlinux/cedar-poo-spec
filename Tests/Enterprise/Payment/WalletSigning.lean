import Examples.Scenarios.FinancialServices.Wallet.Binance2026

namespace CedarPooSpec.WalletSigningTest
open CedarPooSpec.Vertical.FinancialServices PaymentSigning
open CedarPooSpec.WalletSigningExample
open CedarPooSpec.Gateway.EffectProtocol

-- Concrete incident provenance is carried by the shared functional Scenario.
example : CedarPooSpec.Binance2026Scenario.scenario.metadata.value.id = "binance-2026-10-29" := by native_decide
example : CedarPooSpec.Binance2026Scenario.scenario.metadata.value.kind = .reportedIncident := by native_decide
example : (CedarPooSpec.Binance2026Scenario.scenario.ancestors.map (·.id)) =
    ["wallet-native-value-signing"] := by native_decide
example : (CedarPooSpec.Binance2026Scenario.scenario.metadata.value.disclosures.map (·.status)) =
    [.preliminary] := by native_decide

-- Positive controls bind actual C4/Cedar decisions, preparation and final use.
example : (authorization "PaymentGoverned" payment).allowed = true := by native_decide
example : (authorization "PaymentFrozen" payment).allowed = false := by native_decide
example : (authorization "PaymentRestored" payment).allowed = true := by native_decide
example : initialLedger.prepare payment (authorization "PaymentGoverned" payment)
    auditEvidence = some reservedLedger := by native_decide
example : (release current request).isSome = true := by native_decide
example : (prepare ⟨current, request⟩).isOk = true := by native_decide

-- The old ledger owns reservation/dispatch, not current signing authorization.
-- Preserve this counterexample rather than labelling dispatch a current-use gate.
example : (({ reservedLedger with state := { paymentState with
      usedNonces := [payment.nonce], now := 30 } }).dispatch payment.nonce).isSome = true := by
  native_decide
example : release { current with ledger := { reservedLedger with state :=
      { reservedLedger.state with now := 30 } } } request = none := by native_decide

-- Genuine stolen deployment authority is insufficient, even if selected as the
-- expected workload. Renaming its role does not authenticate a signing identity.
example : current.authenticates deployment = true := by decide
example : release current { request with caller := deployment } = none := by native_decide
example : release { current with signer := deployment }
    { request with caller := deployment } = none := by native_decide
example : release current { request with caller :=
    { deployment with purpose := .paymentSigning } } = none := by native_decide
example : release current { request with caller :=
    { signer with release := "malicious-container" } } = none := by native_decide
example : release { current with authenticates := fun _ => false } request = none := by native_decide

-- Every mutation retains the original authentic business approvals and ledger.
def transactionAttacks : List (String × Transaction) := [
  ("recipient", { transaction with beneficiary := "attacker" }),
  ("amount", { transaction with amount := "500.0000" }),
  ("asset", { transaction with asset := "BTC" }),
  ("chain", { transaction with network := "ethereum:10" }),
  ("payer", { transaction with payer := CedarPooSpec.AgentPaymentExample.reserveAccount }),
  ("fee", { transaction with feeCap := "99.0000" }),
  ("nonce", { transaction with nonce := 43 }),
  ("calldata", { transaction with calldata := [1, 2, 3] }),
  ("delegation-kind", { transaction with kind := .delegateCode }),
  ("delegation-code", { transaction with delegatedCode := some "attacker-delegate" }),
  ("delegation-and-code", { transaction with
    kind := .delegateCode, delegatedCode := some "attacker-delegate" }),
  ("clear-is-separate-authority", { transaction with kind := .clearDelegation })]

#guard transactionAttacks.length == 12
#guard (transactionAttacks.map Prod.fst).eraseDups.length == 12
example : transactionAttacks.all (fun (_, tx) =>
    (release current { request with transaction := tx }).isNone) = true := by native_decide

-- Strengthened control: even a self-consistent generic Gateway envelope for the
-- attacker's transaction cannot replace the payment retained by the ledger.
def stolenTransaction : Transaction := { transaction with beneficiary := "attacker" }
def substitutedEffect : EffectIdentity := stolenTransaction.effect payment.nonce 7 signer.subject
def substitutedEnvelope : Envelope := { envelope with effect := substitutedEffect }
def substitutedCurrent : PaymentSigning.Current :=
  { current with gateway := { gateway with effect := substitutedEffect } }
example : accepts substitutedCurrent.gateway substitutedEnvelope true = true := by native_decide
example : release substitutedCurrent { request with
    transaction := stolenTransaction, envelope := substitutedEnvelope } = none := by native_decide

-- Claiming an Allow is insufficient after the trusted C4 assessor freezes it.
example : request.authorization.allowed = true := by native_decide
example : release frozen request = none := by native_decide
example : release current { request with authorization :=
    { request.authorization with verified := false } } = none := by native_decide
example : release current { request with evidence := auditEvidence.take 2 } = none := by native_decide
example : release { current with authenticatesAudit := fun _ => false }
    request = none := by native_decide
example : release current { request with evidence := auditEvidence.map fun item =>
    { item with source := "compromised-ai-tool", verified := true } } = none := by native_decide

def sameReviewer : List AuditEvidence := auditEvidence.map fun item =>
  if item.kind == .human then { item with actor := "one-attacker" } else item
example : release { current with authenticatesAudit := fun _ => true }
    { request with evidence := sameReviewer } = none := by native_decide
example : release { current with ledger := { reservedLedger with state :=
    { reservedLedger.state with now := 25 } } } request = none := by native_decide
example : release { current with ledger := { reservedLedger with state :=
    { reservedLedger.state with policyEpoch := 8 } } } request = none := by native_decide

-- Final-use state, not the original preparation snapshot, controls signing.
example : release { current with gateway := { gateway with revoked := true } }
    request = none := by native_decide
example : release { current with gateway := { gateway with unknown := true } }
    request = none := by native_decide
example : release { current with gateway := { gateway with enforcing := false } }
    request = none := by native_decide
example : release { current with gateway := { gateway with consumed := false } }
    request = none := by native_decide
example : release { current with gateway := { gateway with effect :=
    { effect with generation := 8 } } } request = none := by native_decide
example : release { current with gateway := { gateway with authority :=
    { gateway.authority with now := 25 } } } request = none := by native_decide
example : release { current with chainNonce := 43 } request = none := by native_decide
example : release current { request with operation := "withdrawal-43" } = none := by native_decide
example : release current { request with envelope := { envelope with effect :=
    { effect with payload := "unrelated-approved-hash" } } } = none := by native_decide
example : release { current with
    authorize := authorization "PaymentRestored", gateway := { gateway with revoked := true } } request = none := by native_decide

-- Return the actual submitted ledger. A lost reply cannot issue another signing
-- command through this state; querying the original operation remains read-only.
def afterSigning : Option PaymentSigning.Current := do
  let result ← release current request
  pure { current with ledger := result.ledger }
example : (afterSigning.bind (release · request)) = none := by native_decide
example : (afterSigning.bind fun state => state.ledger.statusQuery payment.nonce).isSome = true := by
  native_decide
example : (afterSigning.bind fun state => state.ledger.cached payment.nonce).map (·.phase) =
    some .submitted := by native_decide
example : ({ reservedLedger with attempts := reservedLedger.attempts ++ reservedLedger.attempts
    } |>.dispatch payment.nonce) = none := by decide

-- Containment gap: pausing withdrawals, revoking local callers and submitting
-- a clearing operation all leave existing on-chain authority outstanding.
example : exposure.pause.code = some "attacker-delegate" := by decide
example : exposure.pause.submitClear.code = some "attacker-delegate" := by decide
example : exposure.observeClear clearObservation = none := by decide
example : (exposure.pause.submitClear.observeClear clearObservation).map (·.code) =
    some none := by decide
example : exposure.pause.submitClear.observeClear
    { clearObservation with finalized := false } = none := by decide
example : exposure.pause.submitClear.observeClear
    { clearObservation with verified := false } = none := by decide
example : exposure.pause.submitClear.observeClear
    { clearObservation with nonce := 42 } = none := by decide
example : exposure.pause.submitClear.observeClear
    { clearObservation with nonce := 44 } = none := by decide
example : exposure.pause.submitClear.observeClear
    { clearObservation with network := "ethereum:10" } = none := by decide
example : exposure.pause.submitClear.observeClear
    { clearObservation with wallet := CedarPooSpec.AgentPaymentExample.reserveAccount } = none := by decide
example : exposure.pause.submitClear.observeClear
    { clearObservation with code := some "replacement-delegate" } = none := by decide

-- Explicit trust counterexample: invented approval identities are refused by
-- the configured verifier but accepted if that trusted verifier lies.
def inventedEvidence : List AuditEvidence := auditEvidence.map fun item =>
  { item with actor := "invented-" ++ item.actor, verified := true }
example : release current { request with evidence := inventedEvidence } = none := by native_decide
example : (release { current with authenticatesAudit := fun _ => true }
    { request with evidence := inventedEvidence }).isSome = true := by native_decide

-- Explicit attacker graph and traces, including acquisition preconditions.
open CedarPooSpec.Attackers CedarPooSpec.Binance2026Scenario
example : decide (Capability.signerNetwork ∈ (run surface foothold path).known) = true := by native_decide
example : (run surface foothold campaign).outputs.length = 0 := by native_decide
example : (run surface foothold campaign).refused = 4 := by native_decide
example : (run surface foothold [.acquire .container]).known = foothold.known := by native_decide
example : (run surface foothold [.acquire .container]).refused = 1 := by native_decide
example : (run surface foothold [.acquire .signerCredential]).known = foothold.known := by native_decide
example : (run surface foothold [.acquire .workflowAuthority]).known = foothold.known := by native_decide
example : (run surface foothold [.call deploymentRequest]).outputs.length = 0 := by native_decide

def legitimate : State Capability PaymentSigning.Current SigningEvent :=
  { known := [.signerNetwork, .signerCredential], world := current }
example : (run surface legitimate [.call request, .call request]).outputs.length = 1 := by native_decide
example : (run surface legitimate [.call request, .call request]).refused = 1 := by native_decide
example : (run surface legitimate [.call request]).outputs.all SigningEvent.safe = true := by native_decide

-- Replacing the real checked writer violates the complete-mediation premise.
-- The same compromise path can then produce an explicitly unsafe effect.
def bypassSurface : Surface Capability PaymentSigning.Request PaymentSigning.Current SigningEvent :=
  { surface with invoke := fun world input => some (world,
      ⟨world, input, ⟨world.ledger, stolenTransaction⟩⟩) }
example : (run bypassSurface foothold (path ++ [.call deploymentRequest])).outputs.length = 1 := by
  native_decide
example : (run bypassSurface foothold (path ++ [.call deploymentRequest])).outputs.all
    SigningEvent.safe = false := by native_decide

#print axioms CedarPooSpec.Attackers.run_preserves_absence
#print axioms CedarPooSpec.Attackers.run_preserves_outputs
#print axioms signing_root_unreachable
#print axioms workflow_root_unreachable
#print axioms attacker_outputs_are_checked
#print axioms reservedPaymentCannotReplay
#print axioms release_requires_current_checks
#print axioms release_returns_requested_transaction
#print axioms release_binds_exact_transaction
#print axioms release_only_native_transfer
#print axioms release_retains_gateway
#print axioms deployment_cannot_release
#print axioms revoked_cannot_release
#print axioms invocation_is_checked
#print axioms pause_preserves_outstanding_authority
#print axioms submission_preserves_outstanding_authority
#print axioms unconfirmed_clear_refused
end CedarPooSpec.WalletSigningTest
