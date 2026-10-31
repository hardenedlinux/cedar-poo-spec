import CedarPooSpec.SchemaJson
import Examples.Governance.AttestedDataAccessExport

namespace CedarPooSpec.AttestedViewsValidatedExport

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← CedarPooSpec.AttestedDataAccessExport.rows
  CedarPooSpec.SchemaJson.manifest
    CedarPooSpec.AttestedDataAccessExample.schema rows

end CedarPooSpec.AttestedViewsValidatedExport
