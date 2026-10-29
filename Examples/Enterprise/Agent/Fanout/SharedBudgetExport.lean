import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Fanout.SharedBudget

/-! Export each admitted or rejected proposal with its pre-admission ledger. -/

namespace CedarPooSpec.SharedBudgetExport

open CedarPooSpec.SharedBudgetExample

def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, root, initial, workers, _) in cases do
    for ((req, _), index) in (replay root initial workers).1.zipIdx do
      let receipt ← CedarPooSpec.SharedBudgetExample.program.authorizationCase
          s!"{name}-step-{index}" root.toLower root req entities
      rows := rows ++ [receipt]
  for (name, root, req) in [
      ("missing-local-base", "Base", missingLocal),
      ("missing-local-integrated", "Integrated", missingLocal),
      ("missing-shared-integrated", "Integrated", missingShared)] do
    let receipt ← CedarPooSpec.SharedBudgetExample.program.authorizationCase name root.toLower root req entities
    rows := rows ++ [receipt]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.SharedBudgetExport
