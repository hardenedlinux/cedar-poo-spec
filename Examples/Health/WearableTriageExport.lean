import CedarPooSpec.Functional.Capabilities
import Examples.Health.WearableTriage

/-! Export each stage of a two-decision remote monitoring flow to Cedar. -/

namespace CedarPooSpec.WearableTriageExport

open CedarPooSpec.WearableTriageExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.WearableTriageExample.model CedarPooSpec.WearableTriageExample.schema :=
      CedarPooSpec.WearableTriageExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, root, observation, facts, _) in cases do
    for ((_, request), index) in (checks root observation facts).zipIdx do
      let receipt ← owner.case
          s!"{name}-layer-{index}" root.toLower root request entities
      rows := rows ++ [receipt]
  return { cases := rows }

end CedarPooSpec.WearableTriageExport
