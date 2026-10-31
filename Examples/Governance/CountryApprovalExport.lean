import CedarPooSpec.Functional.Capabilities
import Examples.Governance.CountryApproval

namespace CedarPooSpec.CountryApprovalExport

open CedarPooSpec.CountryApprovalExample

def rows : Except String (List CedarPooSpec.Transport.Case) :=
  cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.CountryApprovalExample.program.case name root.toLower root req entities

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← rows
  return { cases := exported }

end CedarPooSpec.CountryApprovalExport
