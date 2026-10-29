import CedarPooSpec.Functional.Capabilities
import Examples.Language.ExtensionCoverage

namespace CedarPooSpec.ExtensionCoverageExport

open CedarPooSpec.ExtensionCoverageExample

def manifest : Except String Lean.Json := do
  let exported ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.ExtensionCoverageExample.program.authorizationCase name root.toLower root req entities
  return Lean.Json.mkObj [("cases", Lean.toJson exported)]

end CedarPooSpec.ExtensionCoverageExport
