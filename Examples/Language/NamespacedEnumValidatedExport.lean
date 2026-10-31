import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.SchemaJson
import Examples.Language.NamespacedEnum

namespace CedarPooSpec.NamespacedEnumValidatedExport

open CedarPooSpec.NamespacedEnumExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.NamespacedEnumExample.program.case name root.toLower root req entities
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.NamespacedEnumValidatedExport
