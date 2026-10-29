import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Delegation.AgentDelegation

namespace CedarPooSpec.AgentDelegationExport

open CedarPooSpec.AgentDelegationExample

def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, roots, agent, tool, origin, depth, capability, _) in flowCases do
    for ((root, req), index) in (checks roots agent tool origin depth capability).zipIdx do
      let receipt ← CedarPooSpec.AgentDelegationExample.program.authorizationCase
          s!"{name}-layer-{index}" root.toLower root req entities
      rows := rows ++ [receipt]
  for ((root, req), index) in malformedChecks.zipIdx do
    let receipt ← CedarPooSpec.AgentDelegationExample.program.authorizationCase
        s!"malformed-origin-layer-{index}" root.toLower root req entities
    rows := rows ++ [receipt]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.AgentDelegationExport
