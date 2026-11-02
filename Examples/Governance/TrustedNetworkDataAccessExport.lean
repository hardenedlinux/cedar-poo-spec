import CedarPooSpec.Functional.Capabilities
import Examples.Governance.TrustedNetworkDataAccess

namespace CedarPooSpec.TrustedNetworkDataAccessExport

open CedarPooSpec.TrustedNetworkDataAccessExample

def rows
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.TrustedNetworkDataAccessExample.networkModel CedarPooSpec.TrustedNetworkDataAccessExample.networkSchema :=
      CedarPooSpec.TrustedNetworkDataAccessExample.networkProgram) : Except String (List CedarPooSpec.Transport.Case) :=
  cases.mapM fun (name, root, req, _) =>
    owner.case name root.toLower root req networkEntities

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.TrustedNetworkDataAccessExample.networkModel CedarPooSpec.TrustedNetworkDataAccessExample.networkSchema :=
      CedarPooSpec.TrustedNetworkDataAccessExample.networkProgram) : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← (rows (owner := owner))
  return { cases := exported }

end CedarPooSpec.TrustedNetworkDataAccessExport
