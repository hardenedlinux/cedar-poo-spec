import Examples.Scenarios.FinancialServices.Wallet.Binance2026Replay

namespace CedarPooSpec.WalletReplayTest
open CedarPooSpec.Vertical.FinancialServices
open CedarPooSpec.Binance2026Scenario.Replay

example : CedarPooSpec.Scenarios.Replay.valid scenario.metadata.value stages = true := by native_decide
example : stages.length = 14 := rfl
example : (CedarPooSpec.Attackers.run (surface .guarded)
    { clean.attacker with known := [.signerNetwork, .signerCredential] }
    [.call CedarPooSpec.WalletSigningExample.request,
     .call CedarPooSpec.WalletSigningExample.request]).outputs.length = 1 := by native_decide
example : (summarize (final .bypassCountermodel clean)).signingIntents = 4 := by native_decide
example : (summarize (final .guarded clean)).signingIntents = 0 := by native_decide
example : (summarize (final .guarded priorExposure)).signingIntents = 0 := by native_decide
example : (summarize (final .bypassCountermodel clean)).settled = true := by native_decide
example : (summarize (final .guarded clean)).settled = false := by native_decide
example : (summarize (final .guarded priorExposure)).settled = true := by native_decide
example : (summarize (final .guarded priorExposure)).unknown = true := by native_decide
example : ([final .bypassCountermodel clean, final .guarded clean, final .guarded priorExposure].all
    fun state => (summarize state).paused && !(summarize state).delegated &&
      !(summarize state).signerReachable) = true := by native_decide

def observedAt (id : String) (mode : Mode) (initial : State) : Option Summary :=
  ((frames mode initial).find? fun item => item.1.id == id).map Prod.snd

-- Existing rights and delayed observations survive pause without any new signing.
example : (observedAt "after-pause" .guarded priorExposure).map (·.signingIntents) = some 0 := by native_decide
example : (observedAt "after-pause" .guarded priorExposure).map (·.delegatedUses) = some 1 := by native_decide
example : (observedAt "late-settlement" .guarded priorExposure).map (·.settled) = some true := by native_decide
example : (observedAt "clear-submitted" .guarded priorExposure).map (·.delegated) = some true := by native_decide
example : (observedAt "clear-observed" .guarded priorExposure).map (·.delegated) = some false := by native_decide
example : (observedAt "after-clear" .guarded priorExposure).map (·.delegatedUses) = some 1 := by native_decide
example : (observedAt "restart" .guarded priorExposure).map (·.signingIntents) = some 0 := by native_decide
-- Broken mediation really emits while the same certified key remains isolated.
example : (observedAt "signing-probes" .bypassCountermodel clean).map (·.signingIntents) = some 3 := by native_decide
example : (observedAt "after-pause" .bypassCountermodel clean).map (·.signingIntents) = some 4 := by native_decide

-- Reported, assumed and probe rows cannot silently exchange provenance.
example : CedarPooSpec.Scenarios.Replay.valid scenario.metadata.value (stages ++ stages.take 1) = false := by native_decide
private def emptyStage (description : CedarPooSpec.Scenarios.Replay.Description) :
    CedarPooSpec.Scenarios.Replay.Stage Event := ⟨description, []⟩
example : CedarPooSpec.Scenarios.Replay.valid scenario.metadata.value
    [emptyStage ⟨"missing-source", "Reported claim", .reported, none, none, "not authenticated"⟩] = false := by native_decide
example : CedarPooSpec.Scenarios.Replay.valid scenario.metadata.value
    [emptyStage ⟨"foreign-source", "Reported claim", .reported, some 999, none, "not authenticated"⟩] = false := by native_decide
example : CedarPooSpec.Scenarios.Replay.valid scenario.metadata.value
    [emptyStage ⟨"probe-date", "Probe", .probe, none, some "2026-10-29T23:56:00Z", "invented attribution"⟩] = false := by native_decide
example : CedarPooSpec.Scenarios.Replay.valid scenario.metadata.value
    [emptyStage ⟨"invalid-time", "Reported claim", .reported, some 1, some "2026-99-99", "invalid date"⟩] = false := by native_decide

-- This reconciliation advances only the already submitted attempt. Forged,
-- foreign or incomplete outcomes cannot use the delayed-settlement channel.
def pausedPrior := (step .guarded priorExposure .pause).attacker.world.snapshot
example : (PaymentContainment.observeSettlement pausedPrior settlement).isSome = true := by native_decide
example : (PaymentContainment.observeSettlement pausedPrior { settlement with verified := false }).isNone = true := by native_decide
example : (PaymentContainment.observeSettlement pausedPrior { settlement with idempotencyKey := "foreign" }).isNone = true := by native_decide
example : (PaymentContainment.observeSettlement pausedPrior { settlement with settlement := none }).isNone = true := by native_decide
example : PaymentContainment.release
    ((PaymentContainment.observeSettlement pausedPrior settlement).get (by native_decide))
    CedarPooSpec.WalletSigningExample.request = none := by native_decide

#print axioms PaymentContainment.settlement_retains_exposure
#print axioms PaymentContainment.settlement_cannot_resume
#print axioms PaymentContainment.no_signing_after_pause
#print axioms CedarPooSpec.Attackers.ProfileObject.checked_outputs
#print axioms guarded_outputs_checked
#print axioms bypass_has_no_checked_writer
#print axioms bypass_still_isolates_key
#print axioms CedarPooSpec.Scenarios.Replay.prepared_retains_execution
#print axioms CedarPooSpec.Scenarios.Replay.invocation_retains_execution
end CedarPooSpec.WalletReplayTest
