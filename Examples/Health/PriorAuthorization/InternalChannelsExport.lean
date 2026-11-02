import Examples.Health.PriorAuthorization.InternalChannels

namespace CedarPooSpec.PriorAuthorizationInternalChannelsExport

open CedarPooSpec.PriorAuthorizationInternalChannels

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.PriorAuthorizationInternalChannels.model CedarPooSpec.PriorAuthorizationInternalChannels.schema :=
      CedarPooSpec.PriorAuthorizationInternalChannels.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← LeanPoo.Functional.Validation.traverse (fun (name, root, envelope, _) =>
    owner.case name root root (request envelope) entities) cases
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.PriorAuthorizationInternalChannelsExport
