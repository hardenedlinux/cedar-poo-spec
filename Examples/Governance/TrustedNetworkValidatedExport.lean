import CedarPooSpec.SchemaJson
import Examples.Governance.TrustedNetworkDataAccessExport

namespace CedarPooSpec.TrustedNetworkValidatedExport

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.TrustedNetworkDataAccessExample.networkModel CedarPooSpec.TrustedNetworkDataAccessExample.networkSchema :=
      CedarPooSpec.TrustedNetworkDataAccessExample.networkProgram) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← (CedarPooSpec.TrustedNetworkDataAccessExport.rows (owner := owner))
  CedarPooSpec.SchemaJson.manifest
    CedarPooSpec.TrustedNetworkDataAccessExample.networkSchema rows

end CedarPooSpec.TrustedNetworkValidatedExport
