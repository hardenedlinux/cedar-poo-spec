import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.SchemaJson
import Examples.Language.NamespacedEnum

namespace CedarPooSpec.NamespacedEnumValidatedExport

open CedarPooSpec.NamespacedEnumExample

def manifest : Except String Lean.Json := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.NamespacedEnumExample.program.authorizationCase name root.toLower root req entities
  CedarPooSpec.SchemaJson.validatedManifest schema rows

end CedarPooSpec.NamespacedEnumValidatedExport
