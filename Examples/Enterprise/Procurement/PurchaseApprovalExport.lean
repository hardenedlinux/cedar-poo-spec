import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Procurement.PurchaseApproval

namespace CedarPooSpec.PurchaseApprovalExport

open CedarPooSpec.PurchaseApprovalExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.PurchaseApprovalExample.model CedarPooSpec.PurchaseApprovalExample.schema :=
      CedarPooSpec.PurchaseApprovalExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← cases.mapM fun (name, root, req, _) =>
    owner.case name root.toLower root req entities
  return { cases := exported }

end CedarPooSpec.PurchaseApprovalExport
