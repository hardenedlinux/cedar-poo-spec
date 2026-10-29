import CedarPooSpec.Functional.Reuse
import Examples.Cloud.Pipeline.DeploymentCase

namespace CedarPooSpec.Cloud.Pipeline.DeploymentCase

def manifest : Except String Lean.Json := do
  let source ← (CedarPooSpec.Functional.prepareProgram CedarPooSpec.Functional.standard
    model schema []).mapError CedarPooSpec.Functional.Error.message
  let inputs : List CedarPooSpec.Functional.AuthorizationInput := choices.flatMap fun choice =>
    [⟨s!"{choice.name}-promotion", choice.root, choice.root,
      GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline, entities⟩,
     ⟨s!"{choice.name}-deployment", choice.root, choice.root, deployRequest choice, entities⟩]
  let rows ← source.authorizationCases inputs
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.Cloud.Pipeline.DeploymentCase
