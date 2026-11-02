import CedarPooSpec.Functional.Capabilities
import Examples.Health.MyHealthRecord.Lifecycle

/-! Export the same finite consumer-platform decisions to official Cedar. -/

namespace CedarPooSpec.MyHealthRecordExample.ValidatedExport

open CedarPooSpec.MyHealthRecordExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.MyHealthRecordExample.model CedarPooSpec.MyHealthRecordExample.schema :=
      CedarPooSpec.MyHealthRecordExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    owner.case name root root req entities
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.MyHealthRecordExample.ValidatedExport
