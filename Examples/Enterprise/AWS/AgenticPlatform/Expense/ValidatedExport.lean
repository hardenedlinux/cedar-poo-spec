import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.AWS.AgenticPlatform.Expense.Expense
import CedarPooSpec.SchemaJson

namespace CedarPooSpec.AWS.Expense.ValidatedExport

open CedarPooSpec.AWS.Expense

def manifest : Except String Lean.Json := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.AWS.Expense.program.authorizationCase name root root req entities
  CedarPooSpec.SchemaJson.validatedManifest schema rows

end CedarPooSpec.AWS.Expense.ValidatedExport
