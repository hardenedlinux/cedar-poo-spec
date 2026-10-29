import Examples.Health.PriorAuthorization.InternalChannels

namespace CedarPooSpec.PriorAuthorizationInternalChannelsExport

open CedarPooSpec.PriorAuthorizationInternalChannels

def manifest : Except String Lean.Json := do
  let rows ← LeanPoo.Functional.Validation.traverse (fun (name, root, envelope, _) =>
    program.authorizationCase name root root (request envelope) entities) cases
  CedarPooSpec.SchemaJson.validatedManifest schema rows

end CedarPooSpec.PriorAuthorizationInternalChannelsExport
