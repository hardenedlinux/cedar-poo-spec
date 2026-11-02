import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Session.BoundedSession

/-! Export every step with its pre-admission session facts and materialized POO root. -/

namespace CedarPooSpec.BoundedSessionExport

open CedarPooSpec.BoundedSessionExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.BoundedSessionExample.model CedarPooSpec.BoundedSessionExample.schema :=
      CedarPooSpec.BoundedSessionExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, root, initial, attempts, _) in cases do
    for ((req, _), index) in ((replay (programContext := owner)) root initial attempts).1.zipIdx do
      let receipt ← owner.case
          s!"{name}-step-{index}" root.toLower root req entities
      rows := rows ++ [receipt]
  return { cases := rows }

end CedarPooSpec.BoundedSessionExport
