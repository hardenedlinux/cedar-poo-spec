import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.SchemaJson
import Examples.Language.NamespacedEnum

namespace CedarPooSpec.NamespacedEnumValidatedExport

open CedarPooSpec.NamespacedEnumExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.NamespacedEnumExample.model CedarPooSpec.NamespacedEnumExample.schema :=
      CedarPooSpec.NamespacedEnumExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    owner.case name root.toLower root req entities
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.NamespacedEnumValidatedExport
