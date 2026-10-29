import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Vehicle.Mission.SuccessorBoundary

/-! Export the named successor decisions and their materialized Cedar revisions. -/

namespace CedarPooSpec.SuccessorBoundaryExport

open CedarPooSpec.SuccessorBoundaryExample

def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, root, action, candidate, _) in cases ++ matrixCases do
    let receipt ← CedarPooSpec.SuccessorBoundaryExample.program.authorizationCase
        name root.toLower root (request action candidate) entities
    rows := rows ++ [receipt]
  for (name, req) in [
      ("current-missing-mission-summary", missingMissionSummary),
      ("current-missing-witness-id", missingWitnessId)] do
    let receipt ← CedarPooSpec.SuccessorBoundaryExample.program.authorizationCase name "current" "Current" req entities
    rows := rows ++ [receipt]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.SuccessorBoundaryExport
