import CedarPooSpec.Functional.Reuse
import Examples.Cloud.Pipeline.DeploymentCase

namespace CedarPooSpec.Cloud.Pipeline.DeploymentCase

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.Pipeline.DeploymentCase.model CedarPooSpec.Cloud.Pipeline.DeploymentCase.schema :=
      CedarPooSpec.Cloud.Pipeline.DeploymentCase.program) : Except String CedarPooSpec.Transport.Manifest := do
  let source := owner
  let inputs : List CedarPooSpec.Functional.AuthorizationInput := choices.flatMap fun choice =>
    [⟨s!"{choice.name}-promotion", choice.root, choice.root,
      GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline, entities⟩,
     ⟨s!"{choice.name}-deployment", choice.root, choice.root, deployRequest choice, entities⟩]
  let rows ← source.cases inputs
  return { cases := rows }

end CedarPooSpec.Cloud.Pipeline.DeploymentCase
