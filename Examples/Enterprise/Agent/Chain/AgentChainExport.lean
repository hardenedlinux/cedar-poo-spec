import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Chain.AgentChain

namespace CedarPooSpec.AgentChainExport

open CedarPooSpec.AgentChainExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AgentChainExample.chainModel CedarPooSpec.AgentDelegationExample.schema :=
      CedarPooSpec.AgentChainExample.chainProgram) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, delegationRoot, originRoot, path, origin, _) in cases do
    if validPath path then
      for ((root, req), index) in (checks delegationRoot originRoot path origin).zipIdx do
        let receipt ← owner.case
            s!"{name}-layer-{index}" root.toLower root req chainEntities
        rows := rows ++ [receipt]
  return { cases := rows }

end CedarPooSpec.AgentChainExport
