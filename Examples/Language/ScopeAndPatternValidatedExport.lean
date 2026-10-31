import CedarPooSpec.SchemaJson
import Examples.Language.ScopeAndPatternExport

namespace CedarPooSpec.ScopeAndPatternValidatedExport

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← CedarPooSpec.ScopeAndPatternExport.manifest
  let cases := rows.cases
  CedarPooSpec.SchemaJson.manifest
    CedarPooSpec.ScopeAndPatternExample.schema cases

end CedarPooSpec.ScopeAndPatternValidatedExport
