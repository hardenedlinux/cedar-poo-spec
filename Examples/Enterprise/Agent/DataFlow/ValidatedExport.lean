import CedarPooSpec.SchemaJson
import Examples.Enterprise.Agent.DataFlow.AgentDataFlowExport

namespace CedarPooSpec.AgentDataFlowValidatedExport

open CedarPooSpec.AgentDataFlowExample
open CedarPooSpec.AgentDelegationExample

/-- Replay identical allow and deny requests through both construction roots. -/
def dispatchComparisonRows
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Except String (List CedarPooSpec.Transport.Case) := do
  let requests := [
    ("allow", publishRequest publicDoc publicRepo admin reviewer true),
    ("deny", publishRequest internalDoc publicRepo admin reviewer true)]
  let rows ← LeanPoo.Functional.Validation.traverse (fun (label, req) =>
    LeanPoo.Functional.Validation.traverse (fun root =>
      owner.case s!"dispatch-{label}-{root.toLower}" root.toLower root req dataEntities)
      ["PublishGoverned", "PublishDispatched"]) requests
  return rows.flatten

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← (CedarPooSpec.AgentDataFlowExport.wellFormedRows (owner := owner))
  let comparisons ← (dispatchComparisonRows (owner := owner))
  CedarPooSpec.SchemaJson.manifest
    dataSchema (rows ++ comparisons)

end CedarPooSpec.AgentDataFlowValidatedExport
