import CedarPooSpec.Functional.Reuse
import Examples.Health.PriorAuthorization.PriorAuthorization

namespace CedarPooSpec.PriorAuthorizationValidatedExport

open CedarPooSpec.PriorAuthorizationExample

/-- Every request is captured immediately before its proposed admission. -/
def manifest : Except String Lean.Json := do
  let source ← (CedarPooSpec.Functional.prepareProgram CedarPooSpec.Functional.standard
    model schema []).mapError CedarPooSpec.Functional.Error.message
  let inputs : List CedarPooSpec.Functional.AuthorizationInput :=
    cases.flatMap fun (name, root, state, attempts, _) =>
      (replay root state attempts).1.zipIdx.map fun ((req, _), index) =>
        ⟨s!"{name}-step-{index}", root, root, req, entities⟩
  let rows ← source.authorizationCases inputs
  CedarPooSpec.SchemaJson.validatedManifest schema rows

/-- Raw Cedar replay of a malformed request that schema validation rejects.
    It checks the final positive grant's fail-closed behavior as well. -/
def malformedManifest : Except String Lean.Json := do
  let row ← program.authorizationCase "missing-disclosure-fact" "Governed" "Governed"
    missingDisclosureFact entities
  return Lean.Json.mkObj [("cases", Lean.toJson [row])]

end CedarPooSpec.PriorAuthorizationValidatedExport
