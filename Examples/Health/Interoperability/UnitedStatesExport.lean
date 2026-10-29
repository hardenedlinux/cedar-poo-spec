import CedarPooSpec.Functional.Capabilities
import Examples.Health.Interoperability.UnitedStatesAdmission

/-! Export the finite payer-exchange decisions to official Cedar Rust. -/

namespace CedarPooSpec.UnitedStatesPayerExample.ValidatedExport

open CedarPooSpec.UnitedStatesPayerExample

def manifest : Except String Lean.Json := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.UnitedStatesPayerExample.program.authorizationCase name root root req entities
  let projected ← Admission.projectedCases.mapM fun (name, req, _) =>
    CedarPooSpec.UnitedStatesPayerExample.program.authorizationCase name "Governed" "Governed" req entities
  CedarPooSpec.SchemaJson.validatedManifest schema (rows ++ projected)

end CedarPooSpec.UnitedStatesPayerExample.ValidatedExport
