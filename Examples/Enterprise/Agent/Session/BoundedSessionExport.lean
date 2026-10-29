import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Session.BoundedSession

/-! Export every step with its pre-admission session facts and materialized POO root. -/

namespace CedarPooSpec.BoundedSessionExport

open CedarPooSpec.BoundedSessionExample

def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, root, initial, attempts, _) in cases do
    for ((req, _), index) in (replay root initial attempts).1.zipIdx do
      let receipt ← CedarPooSpec.BoundedSessionExample.program.authorizationCase
          s!"{name}-step-{index}" root.toLower root req entities
      rows := rows ++ [receipt]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.BoundedSessionExport
