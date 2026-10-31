import CedarPooSpec.Functional.Reuse
import Examples.Health.PriorAuthorization.PriorAuthorization

namespace CedarPooSpec.PriorAuthorizationValidatedExport

open CedarPooSpec.PriorAuthorizationExample

/-- Every request is captured immediately before its proposed admission. -/
def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let source ← (CedarPooSpec.Functional.prepareProgram CedarPooSpec.Functional.standard
    model schema []).mapError CedarPooSpec.Functional.Error.message
  let inputs : List CedarPooSpec.Functional.AuthorizationInput :=
    cases.flatMap fun (name, root, state, attempts, _) =>
      (replay root state attempts).1.zipIdx.map fun ((req, _), index) =>
        ⟨s!"{name}-step-{index}", root, root, req, entities⟩
  let rows ← source.cases inputs
  CedarPooSpec.SchemaJson.manifest schema rows

/-- Raw Cedar replay of a malformed request that schema validation rejects.
    It checks the final positive grant's fail-closed behavior as well. -/
def malformedManifest : Except String CedarPooSpec.Transport.Manifest := do
  let row ← program.case "missing-disclosure-fact" "Governed" "Governed"
    missingDisclosureFact entities
  return { cases := [row] }

end CedarPooSpec.PriorAuthorizationValidatedExport
