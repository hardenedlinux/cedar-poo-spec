import CedarPooSpec.Functional.Capabilities
import Examples.Health.Interoperability.Admission

/-! Export the finite upload decisions to official Cedar Rust. -/

namespace CedarPooSpec.AustralianEMRExample.ValidatedExport

open CedarPooSpec.AustralianEMRExample

def manifest : Except String Lean.Json := do
  let rows ← cases.mapM fun (name, root, req, _) =>
    CedarPooSpec.AustralianEMRExample.program.authorizationCase name root root req entities
  let projected ← Admission.projectedCases.mapM fun (name, req, _) =>
    CedarPooSpec.AustralianEMRExample.program.authorizationCase name "Governed" "Governed" req entities
  CedarPooSpec.SchemaJson.validatedManifest schema (rows ++ projected)

end CedarPooSpec.AustralianEMRExample.ValidatedExport
