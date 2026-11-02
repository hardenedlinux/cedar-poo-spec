import Examples.Cloud.Pipeline.GoogleThreatCase

/-! Export the same stage decisions checked in Lean for Cedar Rust replay. -/

namespace CedarPooSpec.Cloud.Pipeline.GoogleThreatCase

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.Pipeline.GoogleThreatCase.model CedarPooSpec.Cloud.Pipeline.GoogleThreatCase.schema :=
      CedarPooSpec.Cloud.Pipeline.GoogleThreatCase.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← LeanPoo.Functional.Validation.traverse (fun (name, root, resource, facts, _) =>
    owner.case name root root
      (request resource facts) entities) cases
  return { cases := rows }

end CedarPooSpec.Cloud.Pipeline.GoogleThreatCase
