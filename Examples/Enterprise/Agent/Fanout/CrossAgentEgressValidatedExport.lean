import CedarPooSpec.Functional.Reuse
import Examples.Enterprise.Agent.Fanout.CrossAgentEgress

namespace CedarPooSpec.CrossAgentEgressValidatedExport

open CedarPooSpec.CrossAgentEgressExample

/-- Export each request with the exact ledger facts seen before admission. -/
def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.CrossAgentEgressExample.model CedarPooSpec.CrossAgentEgressExample.schema :=
      CedarPooSpec.CrossAgentEgressExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let source := owner
  let inputs : List CedarPooSpec.Functional.AuthorizationInput :=
    cases.flatMap fun (name, root, view, attempts, _) =>
      ((replay (programContext := owner)) root view {} attempts).1.zipIdx.map fun ((req, _), index) =>
        ⟨s!"{name}-step-{index}", root, root, req, entities⟩
  let rows ← source.cases inputs
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.CrossAgentEgressValidatedExport
