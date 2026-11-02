import CedarPooSpec.Functional.Capabilities
import Examples.Governance.CountryApproval

namespace CedarPooSpec.CountryApprovalExport

open CedarPooSpec.CountryApprovalExample

def rows
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.CountryApprovalExample.model CedarPooSpec.CountryApprovalExample.schema :=
      CedarPooSpec.CountryApprovalExample.program) : Except String (List CedarPooSpec.Transport.Case) :=
  cases.mapM fun (name, root, req, _) =>
    owner.case name root.toLower root req entities

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.CountryApprovalExample.model CedarPooSpec.CountryApprovalExample.schema :=
      CedarPooSpec.CountryApprovalExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← (rows (owner := owner))
  return { cases := exported }

end CedarPooSpec.CountryApprovalExport
