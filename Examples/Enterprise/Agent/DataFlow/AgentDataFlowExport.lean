import Examples.Enterprise.Agent.DataFlow.AgentDataFlow

namespace CedarPooSpec.AgentDataFlowExport

open CedarPooSpec.AgentDataFlowExample

def wellFormedRows
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Except String (List CedarPooSpec.Transport.Case) := do
  let rows ← LeanPoo.Functional.Validation.traverse
    (fun (name, readRoot, publishRoot, source, repo, origin, approver, approved, _) =>
      LeanPoo.Functional.Validation.traverse (fun ((root, req), index) =>
        owner.case s!"{name}-layer-{index}" root.toLower root req dataEntities)
        (checks readRoot publishRoot source repo origin approver approved).zipIdx) cases
  return rows.flatten

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← (wellFormedRows (owner := owner))
  let malformed ← LeanPoo.Functional.Validation.traverse (fun ((root, req), index) =>
    owner.case s!"malformed-review-layer-{index}" root.toLower root req dataEntities)
    malformedChecks.zipIdx
  return { cases := (rows ++ malformed) }

end CedarPooSpec.AgentDataFlowExport
