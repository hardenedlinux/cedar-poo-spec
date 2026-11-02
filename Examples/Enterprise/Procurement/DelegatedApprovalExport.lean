import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Procurement.DelegatedApproval

namespace CedarPooSpec.DelegatedApprovalExport

open CedarPooSpec.DelegatedApprovalExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.DelegatedApprovalExample.delegatedModel CedarPooSpec.DelegatedApprovalExample.delegatedSchema :=
      CedarPooSpec.DelegatedApprovalExample.delegatedProgram) : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← delegatedCases.mapM fun (name, root, req, _) =>
    owner.case name root.toLower root req delegatedEntities
  return { cases := exported }

end CedarPooSpec.DelegatedApprovalExport
