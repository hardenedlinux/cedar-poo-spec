import CedarPooSpec.Functional.Capabilities
import Examples.Governance.CountryApproval

namespace CedarPooSpec.CountryApprovalExport

open CedarPooSpec.CountryApprovalExample

def rows : Except String (List Lean.Json) :=
  cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.CountryApprovalExample.program.authorizationCase name root.toLower root req entities

def manifest : Except String Lean.Json := do
  let exported ← rows
  return Lean.Json.mkObj [("cases", Lean.toJson exported)]

end CedarPooSpec.CountryApprovalExport
