import CedarPooSpec.Functional.Capabilities
import Examples.Language.ScopeAndPattern

namespace CedarPooSpec.ScopeAndPatternExport

open CedarPooSpec.ScopeAndPatternExample

def manifest : Except String Lean.Json := do
  let exported ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.ScopeAndPatternExample.program.authorizationCase name root.toLower root req entities
  return Lean.Json.mkObj [("cases", Lean.toJson exported)]

end CedarPooSpec.ScopeAndPatternExport
