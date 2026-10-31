import CedarPooSpec.Functional.Capabilities
import Examples.Health.Interoperability.UnitedStatesAdmission

/-! Export the finite payer-exchange decisions to official Cedar Rust. -/

namespace CedarPooSpec.UnitedStatesPayerExample.ValidatedExport

open CedarPooSpec.UnitedStatesPayerExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.UnitedStatesPayerExample.program.case name root root req entities
  let projected ← Admission.projectedCases.mapM fun (name, req, _) =>
    CedarPooSpec.UnitedStatesPayerExample.program.case name "Governed" "Governed" req entities
  CedarPooSpec.SchemaJson.manifest schema (rows ++ projected)

end CedarPooSpec.UnitedStatesPayerExample.ValidatedExport
