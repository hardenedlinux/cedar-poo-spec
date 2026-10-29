import Examples.Enterprise.Agent.Fanout.CrossAgentEgress

namespace CedarPooSpec.CrossAgentEgressValidatedExport

open CedarPooSpec.CrossAgentEgressExample

/-- Export each request with the exact ledger facts seen before admission. -/
def manifest : Except String Lean.Json := do
  let batches ← LeanPoo.Functional.Validation.traverse (fun (name, root, view, attempts, _) =>
    LeanPoo.Functional.Validation.traverse (fun ((req, _), index) =>
      program.authorizationCase s!"{name}-step-{index}" root root req entities)
      (replay root view {} attempts).1.zipIdx) cases
  CedarPooSpec.SchemaJson.validatedManifest schema batches.flatten

end CedarPooSpec.CrossAgentEgressValidatedExport
