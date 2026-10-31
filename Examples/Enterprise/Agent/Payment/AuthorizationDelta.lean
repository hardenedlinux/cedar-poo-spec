import CedarPooSpec.Authorization.Delta.Json
import Examples.Enterprise.Agent.Payment.AgentPayment

/-!
The finance-agent payment graph constrains an existing authorization, then
removes the emergency freeze. SymCC checks all four request types in the
schema and the official Rust authorizer replays the restored grant.
-/

namespace CedarPooSpec.AgentPaymentDelta

open CedarPooSpec.AgentPaymentExample CedarPooSpec.Authorization.Delta

def run : IO Lean.Json := do
  let frozen ← match ← analyzeModel paymentModel "PaymentGoverned" "PaymentFrozen"
      paymentSchema with
    | .ok report => pure report
    | .error error => throw (IO.userError s!"freeze analysis: {reprStr error}")
  if !frozen.noExpansion then
    throw (IO.userError "emergency freeze unexpectedly expands authorization")
  let restored ← match ← analyzeModel paymentModel "PaymentFrozen" "PaymentRestored"
      paymentSchema with
    | .ok report => pure report
    | .error error => throw (IO.userError s!"restore analysis: {reprStr error}")
  if restored.noExpansion then
    throw (IO.userError "restored payment has no expansion witness")
  let .ok frozenJson := CedarPooSpec.Authorization.Delta.Json.report frozen
    | throw (IO.userError "could not render freeze report")
  let .ok restoredJson := CedarPooSpec.Authorization.Delta.Json.report restored
    | throw (IO.userError "could not render restore report")
  let .ok manifest := CedarPooSpec.Authorization.Delta.Json.witnessCases restored
    paymentModel "PaymentFrozen" "PaymentRestored"
    | throw (IO.userError "could not render Cedar payment witness cases")
  return Lean.Json.mkObj [("freeze", frozenJson), ("restore", restoredJson),
    ("manifest", manifest)]

end CedarPooSpec.AgentPaymentDelta

def main : IO Unit := do
  IO.println (← CedarPooSpec.AgentPaymentDelta.run).compress
