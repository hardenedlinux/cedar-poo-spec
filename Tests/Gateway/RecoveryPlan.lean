import CedarPooSpec.Gateway.OAuthReceiver

namespace Tests.Gateway.RecoveryPlan

structure Round where
  handoffsAfterFirst : Nat
  handoffsAfterSecond : Nat
  handoffsAfterConfirmation : Nat
  deriving DecidableEq

def Round.advances (round : Round) : Nat :=
  round.handoffsAfterFirst + round.handoffsAfterSecond + round.handoffsAfterConfirmation

def rounds : List Round := [⟨2, 2, 2⟩, ⟨4, 2, 2⟩, ⟨2, 4, 4⟩]

def Round.toJson (round : Round) : Lean.Json :=
  Lean.Json.mkObj [
    ("handoffs_after_first", Lean.toJson round.handoffsAfterFirst),
    ("handoffs_after_second", Lean.toJson round.handoffsAfterSecond),
    ("handoffs_after_confirmation", Lean.toJson round.handoffsAfterConfirmation),
    ("expected_advances", Lean.toJson round.advances),
    ("expected_crashes", Lean.toJson (3 : Nat))]

def fixture : Lean.Json := Lean.Json.mkObj [
  ("format", Lean.toJson "cedar-poo-legacy-recovery-plan-v1"),
  ("scope", Lean.toJson "settled-read-only-recovery"),
  ("rounds", Lean.Json.arr (rounds.map Round.toJson).toArray)]

end Tests.Gateway.RecoveryPlan
