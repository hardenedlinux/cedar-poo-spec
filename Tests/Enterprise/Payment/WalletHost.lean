import Examples.Scenarios.FinancialServices.Wallet.Binance2026Host

namespace CedarPooSpec.WalletHostTest
open CedarPooSpec.Vertical.FinancialServices
open CedarPooSpec.WalletSigningExample
open CedarPooSpec.Binance2026Scenario.HostBoundary PaymentHost

example : plan.valid := by native_decide
example : (observations.map (·.admitted)) = [true,false,false,false,false,false,false] := by native_decide
example : emitted.bytes = bytes := by native_decide
example : emitted.next.pending = none ∧ emitted.next.unknown = true := by native_decide
example : PaymentHost.prepare host emitted.next (input emitted.next) = none := by native_decide
example : PaymentHost.emit host (emitted.next.refresh current) (input emitted.next) plan ack = none := by native_decide

example : (CedarPooSpec.Attackers.run surface foothold campaign).outputs.length = 0 := by native_decide
example : (CedarPooSpec.Attackers.run surface
    { foothold with known := [.signerNetwork, .signerCredential] }
    [.call (input state), .call (input state)]).outputs.length = 1 := by native_decide

-- Credential substitution cannot select another registrar, scope or command.
example : ([{ credential state with subject := "deployment" },
    { credential state with incarnation := "unreviewed-image" },
    { credential state with publicKey := "attacker-key" },
    { credential state with scope := "deployment" },
    { credential state with audience := "other-signer" },
    { credential state with epoch := 6 }, { credential state with serial := 8 }].all fun binding =>
      (PaymentHost.prepare host state { input state with credential := binding }).isNone) = true := by native_decide

-- Complete, exact, non-claimed, unexpired inventory from the pinned reader.
example : ([[], (facts state).drop 1, facts state ++ [expected state "clock"],
    (facts state).map (fun fact => { fact with origin := .claimed }),
    (facts state).map (fun fact => { fact with issuer := "attacker" }),
    (facts state).map (fun fact => { fact with source := "old-world" }),
    (facts state).map (fun fact => { fact with generation := 6 }),
    (facts state).map (fun fact => { fact with expiresAt := 10 }),
    (facts state).map (fun fact => { fact with value := "invented" })].all fun evidence =>
      (PaymentHost.prepare host state { input state with facts := evidence }).isNone) = true := by native_decide

def expiredHost : Host := { host with source := fun actual => { host.source actual with now := 25 } }
example : PaymentHost.emit expiredHost committed (input committed) plan ack = none := by native_decide
example : (PaymentHost.prepare host state { input state with bytes := [] }).isNone = true := by native_decide
example : (PaymentHost.prepare host state { input state with bytes := [256] }).isNone = true := by native_decide
example : PaymentHost.emit host committed { input committed with bytes := [2,7,43] } plan ack = none := by native_decide

-- A valid ack is bound to the exact before/after journal, bytes and writer cut.
example : ([{ ack with serial := "forged" },
    { ack with plan := { plan with before := { plan.before with writerEpoch := 6 } } },
    { ack with plan := { plan with after := { plan.after with ledger := reservedLedger } } },
    { ack with plan := { plan with command := { plan.command with bytes := [2,7,43] } } }].all fun receipt =>
      (PaymentHost.commit host state (input state) plan receipt).isNone) = true := by native_decide
example : (PaymentHost.commit host { state with snapshot := PaymentContainment.pause state.snapshot }
    (input state) plan ack).isNone = true := by native_decide
example : PaymentHost.emit baseHost committed (input committed) plan ack = none := by native_decide
example : PaymentHost.emit host { committed with writerEpoch := 8 }
    (input committed) plan ack = none := by native_decide
example : PaymentHost.emit host { committed with snapshot := { committed.snapshot with current :=
    { committed.snapshot.current with authorize := frozen.authorize } } }
    (input committed) plan ack = none := by native_decide
example : PaymentHost.emit host { committed with snapshot := { committed.snapshot with current :=
    { committed.snapshot.current with chainNonce := 43 } } }
    (input committed) plan ack = none := by native_decide
example : PaymentHost.emit host { committed with snapshot := { committed.snapshot with current :=
    { committed.snapshot.current with ledger := reservedLedger } } }
    (input committed) plan ack = none := by native_decide

-- Retained Host counterexamples: the fixture is not physical enforcement.
-- If the independently installed verifier lies, a forged ack can be accepted.
def lyingAckHost : Host := { host with verifiesAck := fun _ => true }
example : (PaymentHost.commit lyingAckHost state (input state) plan
    { ack with serial := "forged" }).isSome = true := by native_decide
-- Pure immutable snapshots are reusable; native antirollback/complete mediation
-- must prevent using this same old committed state twice in the real signer.
example : ([committed, committed].all fun old =>
    (PaymentHost.emit host old (input old) plan ack).isSome) = true := by native_decide
-- Equality with an installed decoder cannot prove the chain's actual codec.
def otherChainMeaning (_ : Bytes) : Option PaymentSigning.Transaction :=
  some { transaction with beneficiary := "attacker" }
example : otherChainMeaning bytes ≠ host.decode bytes := by native_decide
example : (PaymentHost.prepare host state (input state)).isSome = true := by native_decide

#print axioms emission_returns_exact_bytes
#print axioms emission_requires_durable_plan
#print axioms emission_retains_registrar
#print axioms emission_retains_facts
#print axioms emission_requires_current_cut
#print axioms no_second_emission
#print axioms unknown_cannot_prepare
#print axioms requirement_preserves_original
#print axioms invocation_retains_plan
end CedarPooSpec.WalletHostTest
