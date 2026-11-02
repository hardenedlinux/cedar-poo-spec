import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Delegation.AgentDelegation

namespace CedarPooSpec.AgentDelegationExport

open CedarPooSpec.AgentDelegationExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AgentDelegationExample.model CedarPooSpec.AgentDelegationExample.schema :=
      CedarPooSpec.AgentDelegationExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, roots, agent, tool, origin, depth, capability, _) in flowCases do
    for ((root, req), index) in (checks roots agent tool origin depth capability).zipIdx do
      let receipt ← owner.case
          s!"{name}-layer-{index}" root.toLower root req entities
      rows := rows ++ [receipt]
  for ((root, req), index) in malformedChecks.zipIdx do
    let receipt ← owner.case
        s!"malformed-origin-layer-{index}" root.toLower root req entities
    rows := rows ++ [receipt]
  return { cases := rows }

end CedarPooSpec.AgentDelegationExport
