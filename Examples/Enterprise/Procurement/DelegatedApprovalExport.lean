import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Procurement.DelegatedApproval

namespace CedarPooSpec.DelegatedApprovalExport

open CedarPooSpec.DelegatedApprovalExample

def manifest : Except String Lean.Json := do
  let exported ← delegatedCases.mapM fun (name, root, req, _) =>
    CedarPooSpec.DelegatedApprovalExample.delegatedProgram.authorizationCase name root.toLower root req delegatedEntities
  return Lean.Json.mkObj [("cases", Lean.toJson exported)]

end CedarPooSpec.DelegatedApprovalExport
