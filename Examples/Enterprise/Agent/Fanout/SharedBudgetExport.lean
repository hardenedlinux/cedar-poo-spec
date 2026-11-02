import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Fanout.SharedBudget

/-! Export each admitted or rejected proposal with its pre-admission ledger. -/

namespace CedarPooSpec.SharedBudgetExport

open CedarPooSpec.SharedBudgetExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.SharedBudgetExample.model CedarPooSpec.SharedBudgetExample.schema :=
      CedarPooSpec.SharedBudgetExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, root, initial, workers, _) in cases do
    for ((req, _), index) in ((replay (programContext := owner)) root initial workers).1.zipIdx do
      let receipt ← owner.case
          s!"{name}-step-{index}" root.toLower root req entities
      rows := rows ++ [receipt]
  for (name, root, req) in [
      ("missing-local-base", "Base", missingLocal),
      ("missing-local-integrated", "Integrated", missingLocal),
      ("missing-shared-integrated", "Integrated", missingShared)] do
    let receipt ← owner.case name root.toLower root req entities
    rows := rows ++ [receipt]
  return { cases := rows }

end CedarPooSpec.SharedBudgetExport
