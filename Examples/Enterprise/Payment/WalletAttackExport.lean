import Examples.Enterprise.Payment.WalletAttack
import Lean.Data.Json

namespace CedarPooSpec.WalletAttackExample

private def quoted (text : String) : String := (Lean.toJson text).compress
private def name (cap : Capability) : String := ((reprStr cap).splitOn ".").getLast!
private def setOf (items : List String) : String := "Set(" ++ String.intercalate ", " items ++ ")"

/-- Quint consumes the actual checked POO model; no second compromise graph is
maintained in the finite-state case. Generation fails when either parent drops. -/
def exportQuint : Except String String := do
  let checked ← match selectedModel with
    | some model => .ok model
    | none => .error "attacker object admission failed"
  let initial := setOf (checked.model.initial.map (quoted ∘ name))
  let isolated := setOf (checked.model.isolated.map (quoted ∘ name))
  let goals := setOf (checked.model.goals.map quoted)
  let rules := setOf (checked.model.rules.map fun rule =>
    "{ needs: " ++ setOf (rule.requires.map (quoted ∘ name)) ++ ", grants: " ++ quoted (name rule.grants) ++ " }")
  pure (String.intercalate "\n" [
    "// Generated from checked LeanPoo slots; do not edit.",
    "module wallet_attackers_profile {",
    "  pure val Initial: Set[str] = " ++ initial,
    "  pure val Isolated: Set[str] = " ++ isolated,
    "  pure val Goals: Set[str] = " ++ goals,
    "  pure val Rules: Set[{needs: Set[str], grants: str}] = " ++ rules,
    "}", ""])


end CedarPooSpec.WalletAttackExample

def main : IO Unit := match CedarPooSpec.WalletAttackExample.exportQuint with
  | .ok source => IO.print source
  | .error error => throw (IO.userError error)
