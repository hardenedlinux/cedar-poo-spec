import CedarPooSpec.SchemaJson
import Examples.Governance.TrustedNetworkDataAccessExport

namespace CedarPooSpec.TrustedNetworkValidatedExport

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← CedarPooSpec.TrustedNetworkDataAccessExport.rows
  CedarPooSpec.SchemaJson.manifest
    CedarPooSpec.TrustedNetworkDataAccessExample.networkSchema rows

end CedarPooSpec.TrustedNetworkValidatedExport
