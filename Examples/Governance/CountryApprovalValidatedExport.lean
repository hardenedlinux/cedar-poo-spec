import CedarPooSpec.SchemaJson
import Examples.Governance.CountryApprovalExport

namespace CedarPooSpec.CountryApprovalValidatedExport

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.CountryApprovalExample.model CedarPooSpec.CountryApprovalExample.schema :=
      CedarPooSpec.CountryApprovalExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← (CedarPooSpec.CountryApprovalExport.rows (owner := owner))
  CedarPooSpec.SchemaJson.manifest
    CedarPooSpec.CountryApprovalExample.schema rows

end CedarPooSpec.CountryApprovalValidatedExport
