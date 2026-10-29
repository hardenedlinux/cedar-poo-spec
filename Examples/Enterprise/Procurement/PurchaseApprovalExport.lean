import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Procurement.PurchaseApproval

namespace CedarPooSpec.PurchaseApprovalExport

open CedarPooSpec.PurchaseApprovalExample

def manifest : Except String Lean.Json := do
  let exported ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.PurchaseApprovalExample.program.authorizationCase name root.toLower root req entities
  return Lean.Json.mkObj [("cases", Lean.toJson exported)]

end CedarPooSpec.PurchaseApprovalExport
