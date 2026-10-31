import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Vehicle.VLA.CommandBoundary

/-! Export the same named decisions and materialized policy revisions. -/

namespace CedarPooSpec.VlaCommandBoundaryExport

open CedarPooSpec.VlaCommandBoundaryExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, root, action, segment, facts, _) in cases do
    let receipt ← CedarPooSpec.VlaCommandBoundaryExample.program.case
        name root.toLower root (request action segment facts) entities
    rows := rows ++ [receipt]
  return { cases := rows }

end CedarPooSpec.VlaCommandBoundaryExport
