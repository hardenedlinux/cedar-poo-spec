import CedarPooSpec.SchemaJson
import Examples.Enterprise.Agent.DataFlow.AgentDataFlowExport

namespace CedarPooSpec.AgentDataFlowValidatedExport

open CedarPooSpec.AgentDataFlowExample
open CedarPooSpec.AgentDelegationExample

/-- Replay identical allow and deny requests through both construction roots. -/
def dispatchComparisonRows : Except String (List Lean.Json) := do
  let requests := [
    ("allow", publishRequest publicDoc publicRepo admin reviewer true),
    ("deny", publishRequest internalDoc publicRepo admin reviewer true)]
  let rows ← LeanPoo.Functional.Validation.traverse (fun (label, req) =>
    LeanPoo.Functional.Validation.traverse (fun root =>
      program.authorizationCase s!"dispatch-{label}-{root.toLower}" root.toLower root req dataEntities)
      ["PublishGoverned", "PublishDispatched"]) requests
  return rows.flatten

def manifest : Except String Lean.Json := do
  let rows ← CedarPooSpec.AgentDataFlowExport.wellFormedRows
  let comparisons ← dispatchComparisonRows
  CedarPooSpec.SchemaJson.validatedManifest
    dataSchema (rows ++ comparisons)

end CedarPooSpec.AgentDataFlowValidatedExport
