import CedarPooSpec.SchemaJson
import Examples.Governance.CountryApprovalExport

namespace CedarPooSpec.CountryApprovalValidatedExport

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← CedarPooSpec.CountryApprovalExport.rows
  CedarPooSpec.SchemaJson.manifest
    CedarPooSpec.CountryApprovalExample.schema rows

end CedarPooSpec.CountryApprovalValidatedExport
