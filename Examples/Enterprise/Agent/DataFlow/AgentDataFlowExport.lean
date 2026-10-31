import Examples.Enterprise.Agent.DataFlow.AgentDataFlow

namespace CedarPooSpec.AgentDataFlowExport

open CedarPooSpec.AgentDataFlowExample

def wellFormedRows : Except String (List CedarPooSpec.Transport.Case) := do
  let rows ← LeanPoo.Functional.Validation.traverse
    (fun (name, readRoot, publishRoot, source, repo, origin, approver, approved, _) =>
      LeanPoo.Functional.Validation.traverse (fun ((root, req), index) =>
        program.case s!"{name}-layer-{index}" root.toLower root req dataEntities)
        (checks readRoot publishRoot source repo origin approver approved).zipIdx) cases
  return rows.flatten

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← wellFormedRows
  let malformed ← LeanPoo.Functional.Validation.traverse (fun ((root, req), index) =>
    program.case s!"malformed-review-layer-{index}" root.toLower root req dataEntities)
    malformedChecks.zipIdx
  return { cases := (rows ++ malformed) }

end CedarPooSpec.AgentDataFlowExport
