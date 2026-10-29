import Examples.Enterprise.Agent.DataFlow.AgentDataFlow

namespace CedarPooSpec.AgentDataFlowExport

open CedarPooSpec.AgentDataFlowExample

def wellFormedRows : Except String (List Lean.Json) := do
  let rows ← LeanPoo.Functional.Validation.traverse
    (fun (name, readRoot, publishRoot, source, repo, origin, approver, approved, _) =>
      LeanPoo.Functional.Validation.traverse (fun ((root, req), index) =>
        program.authorizationCase s!"{name}-layer-{index}" root.toLower root req dataEntities)
        (checks readRoot publishRoot source repo origin approver approved).zipIdx) cases
  return rows.flatten

def manifest : Except String Lean.Json := do
  let rows ← wellFormedRows
  let malformed ← LeanPoo.Functional.Validation.traverse (fun ((root, req), index) =>
    program.authorizationCase s!"malformed-review-layer-{index}" root.toLower root req dataEntities)
    malformedChecks.zipIdx
  return Lean.Json.mkObj [("cases", Lean.toJson (rows ++ malformed))]

end CedarPooSpec.AgentDataFlowExport
