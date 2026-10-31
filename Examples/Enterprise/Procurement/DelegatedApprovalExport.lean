import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Procurement.DelegatedApproval

namespace CedarPooSpec.DelegatedApprovalExport

open CedarPooSpec.DelegatedApprovalExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← delegatedCases.mapM fun (name, root, req, _) =>
    CedarPooSpec.DelegatedApprovalExample.delegatedProgram.case name root.toLower root req delegatedEntities
  return { cases := exported }

end CedarPooSpec.DelegatedApprovalExport
