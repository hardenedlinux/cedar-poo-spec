import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Procurement.PurchaseApproval

namespace CedarPooSpec.PurchaseApprovalExport

open CedarPooSpec.PurchaseApprovalExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.PurchaseApprovalExample.program.case name root.toLower root req entities
  return { cases := exported }

end CedarPooSpec.PurchaseApprovalExport
