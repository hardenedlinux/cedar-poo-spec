import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Vehicle.VLA.CommandBoundary

/-! Export the same named decisions and materialized policy revisions. -/

namespace CedarPooSpec.VlaCommandBoundaryExport

open CedarPooSpec.VlaCommandBoundaryExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.VlaCommandBoundaryExample.model CedarPooSpec.VlaCommandBoundaryExample.schema :=
      CedarPooSpec.VlaCommandBoundaryExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, root, action, segment, facts, _) in cases do
    let receipt ← owner.case
        name root.toLower root (request action segment facts) entities
    rows := rows ++ [receipt]
  return { cases := rows }

end CedarPooSpec.VlaCommandBoundaryExport
