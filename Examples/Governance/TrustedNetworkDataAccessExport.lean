import CedarPooSpec.Functional.Capabilities
import Examples.Governance.TrustedNetworkDataAccess

namespace CedarPooSpec.TrustedNetworkDataAccessExport

open CedarPooSpec.TrustedNetworkDataAccessExample

def rows : Except String (List Lean.Json) :=
  cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.TrustedNetworkDataAccessExample.networkProgram.authorizationCase name root.toLower root req networkEntities

def manifest : Except String Lean.Json := do
  let exported ← rows
  return Lean.Json.mkObj [("cases", Lean.toJson exported)]

end CedarPooSpec.TrustedNetworkDataAccessExport
