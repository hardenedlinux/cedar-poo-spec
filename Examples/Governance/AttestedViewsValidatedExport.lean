import CedarPooSpec.SchemaJson
import Examples.Governance.AttestedDataAccessExport

namespace CedarPooSpec.AttestedViewsValidatedExport

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AttestedDataAccessExample.model CedarPooSpec.AttestedDataAccessExample.schema :=
      CedarPooSpec.AttestedDataAccessExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← (CedarPooSpec.AttestedDataAccessExport.rows (owner := owner))
  CedarPooSpec.SchemaJson.manifest
    CedarPooSpec.AttestedDataAccessExample.schema rows

end CedarPooSpec.AttestedViewsValidatedExport
