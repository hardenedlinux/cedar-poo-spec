import Examples.Health.PriorAuthorization.PriorAuthorization

namespace CedarPooSpec.PriorAuthorizationValidatedExport

open CedarPooSpec.PriorAuthorizationExample

/-- Every request is captured immediately before its proposed admission. -/
def manifest : Except String Lean.Json := do
  let rows ← LeanPoo.Functional.Validation.traverse (fun (name, root, state, attempts, _) =>
    LeanPoo.Functional.Validation.traverse (fun ((req, _), index) =>
      program.authorizationCase s!"{name}-step-{index}" root root req entities)
      (replay root state attempts).1.zipIdx) cases
  CedarPooSpec.SchemaJson.validatedManifest schema rows.flatten

/-- Raw Cedar replay of a malformed request that schema validation rejects.
    It checks the final positive grant's fail-closed behavior as well. -/
def malformedManifest : Except String Lean.Json := do
  let row ← program.authorizationCase "missing-disclosure-fact" "Governed" "Governed"
    missingDisclosureFact entities
  return Lean.Json.mkObj [("cases", Lean.toJson [row])]

end CedarPooSpec.PriorAuthorizationValidatedExport
