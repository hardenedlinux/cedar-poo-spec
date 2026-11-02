import CedarPooSpec.Functional.Capabilities
import Examples.Language.ExtensionCoverage

namespace CedarPooSpec.ExtensionCoverageExport

open CedarPooSpec.ExtensionCoverageExample

def manifest
    (owner : CedarPooSpec.Functional.Compilation CedarPooSpec.ExtensionCoverageExample.model :=
      CedarPooSpec.ExtensionCoverageExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← cases.mapM fun (name, root, req, _) =>
    owner.case name root.toLower root req entities
  return { cases := exported }

end CedarPooSpec.ExtensionCoverageExport
