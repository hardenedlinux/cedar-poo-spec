import CedarPooSpec.Functional.Capabilities
import Examples.Health.WearableTriage

/-! Export each stage of a two-decision remote monitoring flow to Cedar. -/

namespace CedarPooSpec.WearableTriageExport

open CedarPooSpec.WearableTriageExample

def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, root, observation, facts, _) in cases do
    for ((_, request), index) in (checks root observation facts).zipIdx do
      let receipt ← CedarPooSpec.WearableTriageExample.program.authorizationCase
          s!"{name}-layer-{index}" root.toLower root request entities
      rows := rows ++ [receipt]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.WearableTriageExport
