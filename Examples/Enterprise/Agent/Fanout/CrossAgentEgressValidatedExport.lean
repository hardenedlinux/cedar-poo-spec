import CedarPooSpec.Functional.Reuse
import Examples.Enterprise.Agent.Fanout.CrossAgentEgress

namespace CedarPooSpec.CrossAgentEgressValidatedExport

open CedarPooSpec.CrossAgentEgressExample

/-- Export each request with the exact ledger facts seen before admission. -/
def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let source ← (CedarPooSpec.Functional.prepareProgram CedarPooSpec.Functional.standard
    model schema []).mapError CedarPooSpec.Functional.Error.message
  let inputs : List CedarPooSpec.Functional.AuthorizationInput :=
    cases.flatMap fun (name, root, view, attempts, _) =>
      (replay root view {} attempts).1.zipIdx.map fun ((req, _), index) =>
        ⟨s!"{name}-step-{index}", root, root, req, entities⟩
  let rows ← source.cases inputs
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.CrossAgentEgressValidatedExport
