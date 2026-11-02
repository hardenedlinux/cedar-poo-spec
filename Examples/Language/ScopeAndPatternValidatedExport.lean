import CedarPooSpec.SchemaJson
import Examples.Language.ScopeAndPatternExport

namespace CedarPooSpec.ScopeAndPatternValidatedExport

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.ScopeAndPatternExample.model CedarPooSpec.ScopeAndPatternExample.schema :=
      CedarPooSpec.ScopeAndPatternExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← (CedarPooSpec.ScopeAndPatternExport.manifest (owner := owner))
  let cases := rows.cases
  CedarPooSpec.SchemaJson.manifest
    CedarPooSpec.ScopeAndPatternExample.schema cases

end CedarPooSpec.ScopeAndPatternValidatedExport
