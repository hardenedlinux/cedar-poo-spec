import Examples.Scenarios.FinancialServices.Wallet.Binance2026
import Lean.Data.Json

namespace CedarPooSpec.Binance2026Scenario

private def quoted (text : String) : String := (Lean.toJson text).compress
private def name (cap : Capability) : String := ((reprStr cap).splitOn ".").getLast!
private def setOf (items : List String) : String := "Set(" ++ String.intercalate ", " items ++ ")"

/-- Quint consumes the actual checked POO model; no second compromise graph is
maintained in the finite-state case. Generation fails when either parent drops. -/
def exportQuint : Except String String := do
  let checked ← match selectedModel with
    | some model => .ok model
    | none => .error "attacker object admission failed"
  if checked.model != scenario.model.2.model then
    .error "scenario/attacker model mismatch"
  let initial := setOf (checked.model.initial.map (quoted ∘ name))
  let isolated := setOf (checked.model.isolated.map (quoted ∘ name))
  let goals := setOf (checked.model.goals.map quoted)
  let rules := setOf (checked.model.rules.map fun rule =>
    "{ needs: " ++ setOf (rule.requires.map (quoted ∘ name)) ++ ", grants: " ++ quoted (name rule.grants) ++ " }")
  pure (String.intercalate "\n" [
    "// Generated from checked LeanPoo slots; do not edit.",
    "module wallet_attackers_case {",
    "  pure val ProfileInitial: Set[str] = " ++ initial,
    "  pure val ProfileIsolated: Set[str] = " ++ isolated,
    "  pure val ProfileGoals: Set[str] = " ++ goals,
    "  pure val ProfileRules: Set[{needs: Set[str], grants: str}] = " ++ rules,
    "  import wallet_signing(Initial = ProfileInitial, Isolated = ProfileIsolated, Goals = ProfileGoals, Rules = ProfileRules).* from " ++ quoted "../../dev/qnt/financial/WalletSigning",
    "}", ""])

/-- Observed synthetic outcomes for the illustrated defense path, not production telemetry. -/
def exportVisual : Lean.Json :=
  let current := CedarPooSpec.WalletSigningExample.current
  let request := CedarPooSpec.WalletSigningExample.request
  Lean.Json.mkObj [
    ("provenance", scenario.provenanceJson),
    ("defense", Lean.Json.mkObj [
      ("deployment_refused", Lean.toJson (CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release
        current deploymentRequest).isNone),
      ("valid_transfer_released", Lean.toJson (CedarPooSpec.Vertical.FinancialServices.PaymentSigning.release
        current request).isSome)])]


end CedarPooSpec.Binance2026Scenario

def main (args : List String) : IO Unit :=
  match args with
  | ["visual"] => IO.println CedarPooSpec.Binance2026Scenario.exportVisual.compress
  | ["metadata"] => IO.println CedarPooSpec.Binance2026Scenario.scenario.provenanceJson.compress
  | [] => match CedarPooSpec.Binance2026Scenario.exportQuint with
    | .ok source => IO.print source
    | .error error => throw (IO.userError error)
  | _ => throw (IO.userError "expected no arguments, metadata or visual")
