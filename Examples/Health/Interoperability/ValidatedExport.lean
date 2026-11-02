import CedarPooSpec.Functional.Capabilities
import Examples.Health.Interoperability.Admission

/-! Export the finite upload decisions to official Cedar Rust. -/

namespace CedarPooSpec.AustralianEMRExample.ValidatedExport

open CedarPooSpec.AustralianEMRExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AustralianEMRExample.model CedarPooSpec.AustralianEMRExample.schema :=
      CedarPooSpec.AustralianEMRExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    owner.case name root root req entities
  let projected ← Admission.projectedCases.mapM fun (name, req, _) =>
    owner.case name "Governed" "Governed" req entities
  CedarPooSpec.SchemaJson.manifest schema (rows ++ projected)

end CedarPooSpec.AustralianEMRExample.ValidatedExport
