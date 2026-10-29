import CedarPooSpec.Functional.Reuse
import Examples.Cloud.DataProtection.GoogleSdpRelease

namespace CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease

open CedarPooSpec.Cloud.Pipeline

def manifest : Except String Lean.Json := do
  let source ← (CedarPooSpec.Functional.prepareProgram CedarPooSpec.Functional.standard
    model schema []).mapError CedarPooSpec.Functional.Error.message
  let inputs : List CedarPooSpec.Functional.AuthorizationInput := choices.flatMap fun choice =>
    [⟨s!"{choice.name}-pipeline", choice.root, choice.root,
      GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline, entities⟩,
     ⟨s!"{choice.name}-transform", choice.root, choice.root, transformRequest choice, entities⟩]
  let rows ← source.authorizationCases inputs
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease
