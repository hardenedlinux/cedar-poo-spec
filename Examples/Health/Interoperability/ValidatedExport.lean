import CedarPooSpec.Functional.Capabilities
import Examples.Health.Interoperability.Admission

/-! Export the finite upload decisions to official Cedar Rust. -/

namespace CedarPooSpec.AustralianEMRExample.ValidatedExport

open CedarPooSpec.AustralianEMRExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.AustralianEMRExample.program.case name root root req entities
  let projected ← Admission.projectedCases.mapM fun (name, req, _) =>
    CedarPooSpec.AustralianEMRExample.program.case name "Governed" "Governed" req entities
  CedarPooSpec.SchemaJson.manifest schema (rows ++ projected)

end CedarPooSpec.AustralianEMRExample.ValidatedExport
