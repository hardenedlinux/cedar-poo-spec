import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.AWS.AgenticPlatform.Expense.Expense
import CedarPooSpec.SchemaJson

namespace CedarPooSpec.AWS.Expense.ValidatedExport

open CedarPooSpec.AWS.Expense

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AWS.Expense.model CedarPooSpec.AWS.Expense.schema :=
      CedarPooSpec.AWS.Expense.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    owner.case name root root req entities
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.AWS.Expense.ValidatedExport
