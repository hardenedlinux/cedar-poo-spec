import Examples.Scenarios.FinancialServices.Wallet.Binance2026

namespace CedarPooSpec.WalletContainmentTest
open CedarPooSpec.Vertical.FinancialServices
open CedarPooSpec.WalletSigningExample
open CedarPooSpec.Binance2026Scenario

-- Retain the old composition gap as negative evidence: updating an isolated
-- exposure object does not revoke an unrelated current-use signing snapshot.
example : exposure.pause.withdrawalsPaused = true := rfl
example : (PaymentSigning.release current request).isSome = true := by native_decide
example : (PaymentContainment.release Containment.clean request).isSome = true := by native_decide
example : PaymentContainment.release Containment.exposed request = none := by native_decide
example : PaymentContainment.release Containment.paused request = none := by native_decide
example : PaymentContainment.release (PaymentContainment.recover Containment.paused current) request = none := by native_decide
example : (PaymentContainment.pause Containment.clean).current.gateway.revoked = true := rfl
example : PaymentContainment.release Containment.clean deploymentRequest = none := by native_decide
example : PaymentContainment.release { Containment.clean with current := frozen } request = none := by native_decide
example : PaymentContainment.release { Containment.clean with exposure :=
    { Containment.clean.exposure with wallet := CedarPooSpec.AgentPaymentExample.reserveAccount } }
    request = none := by native_decide
example : PaymentContainment.release { Containment.clean with exposure :=
    { Containment.clean.exposure with network := "ethereum:10" } } request = none := by native_decide
example : (PaymentContainment.submitClear Containment.exposed).isNone = true := by native_decide
example : (PaymentContainment.observeClear Containment.paused clearObservation).isNone = true := by native_decide
example : Containment.submitted.exposure.code = exposure.code := by native_decide

def signed := (PaymentContainment.release Containment.clean request).get (by native_decide)
def consumed : PaymentContainment.Snapshot :=
  { Containment.clean with current := { current with ledger := signed.ledger } }
example : PaymentContainment.release (PaymentContainment.recover consumed current) request = none := by native_decide
example : (PaymentContainment.recover consumed current).current.ledger.state.usedNonces =
    consumed.current.ledger.state.usedNonces := rfl

-- A claimed removal needs the exact, independently verified final observation.
example : ([{ clearObservation with finalized := false },
    { clearObservation with verified := false }, { clearObservation with nonce := 42 },
    { clearObservation with nonce := 44 }, { clearObservation with network := "ethereum:10" },
    { clearObservation with wallet := CedarPooSpec.AgentPaymentExample.reserveAccount },
    { clearObservation with code := some "replacement-delegate" }].all fun observation =>
      (PaymentContainment.observeClear Containment.submitted observation).isNone) = true := by native_decide
example : Containment.cleared.exposure.code = none := by native_decide
example : Containment.cleared.exposure.withdrawalsPaused = true := by native_decide
example : PaymentContainment.release Containment.cleared request = none := by native_decide
example : PaymentContainment.release Containment.recovered request = none := by native_decide
example : PaymentContainment.release (PaymentContainment.run (PaymentContainment.pause Containment.exposed)
    [.recover current, .submitClear, .observeClear clearObservation, .recover current])
    request = none := by native_decide
example : (PaymentContainment.prepare ⟨Containment.paused, request⟩).isOk = false := by native_decide

-- Reaching the service is distinct from producing an effect. All observations
-- come from the admitted C4 family and its original trace prefixes.
example : (replayStages.map (·.reached)) = [true, true, true, true] := by native_decide
example : (replayStages.map (·.signatures)) = [0, 0, 0, 0] := by native_decide
example : (replayStages.map (·.refused)) = [0, 0, 0, 1] := by native_decide
example : (replayStages.map (·.signerReachable)) = [false, false, false, true] := by native_decide

def admittedSigner : CedarPooSpec.Attackers.State Capability PaymentContainment.Snapshot SigningEvent :=
  { known := [.signerNetwork, .signerCredential], world := Containment.clean }
example : (CedarPooSpec.Attackers.run Containment.surface admittedSigner
    [.call request, .call request]).outputs.length = 1 := by native_decide
example : (CedarPooSpec.Attackers.run Containment.surface
    { admittedSigner with world := PaymentContainment.pause Containment.clean }
    [.call request]).outputs.length = 0 := by native_decide
example : (CedarPooSpec.Attackers.run Containment.surface Containment.foothold campaign).outputs.length = 0 := by native_decide

#print axioms PaymentContainment.release_retains_signing
#print axioms PaymentContainment.release_binds_wallet
#print axioms PaymentContainment.pause_blocks_signing
#print axioms PaymentContainment.no_signing_after_pause
#print axioms PaymentContainment.observation_cannot_resume
#print axioms PaymentContainment.invocation_retains_checks
end CedarPooSpec.WalletContainmentTest
