import CedarPooSpec.Functional.Capabilities
import Examples.Language.ScopeAndPattern

namespace CedarPooSpec.ScopeAndPatternExport

open CedarPooSpec.ScopeAndPatternExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.ScopeAndPatternExample.model CedarPooSpec.ScopeAndPatternExample.schema :=
      CedarPooSpec.ScopeAndPatternExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let exported ← cases.mapM fun (name, root, req, _) =>
    owner.case name root.toLower root req entities
  return { cases := exported }

end CedarPooSpec.ScopeAndPatternExport
