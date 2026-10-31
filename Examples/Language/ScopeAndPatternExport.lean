import CedarPooSpec.Functional.Capabilities
import Examples.Language.ScopeAndPattern

namespace CedarPooSpec.ScopeAndPatternExport

open CedarPooSpec.ScopeAndPatternExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.ScopeAndPatternExample.program.case name root.toLower root req entities
  return { cases := exported }

end CedarPooSpec.ScopeAndPatternExport
