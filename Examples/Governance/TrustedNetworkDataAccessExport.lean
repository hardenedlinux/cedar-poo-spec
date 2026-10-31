import CedarPooSpec.Functional.Capabilities
import Examples.Governance.TrustedNetworkDataAccess

namespace CedarPooSpec.TrustedNetworkDataAccessExport

open CedarPooSpec.TrustedNetworkDataAccessExample

def rows : Except String (List CedarPooSpec.Transport.Case) :=
  cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.TrustedNetworkDataAccessExample.networkProgram.case name root.toLower root req networkEntities

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← rows
  return { cases := exported }

end CedarPooSpec.TrustedNetworkDataAccessExport
