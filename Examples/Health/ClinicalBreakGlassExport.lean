import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import Examples.Health.ClinicalBreakGlass

/-! Export clinical POO revisions and Lean-computed authorization receipts. -/

namespace CedarPooSpec.ClinicalBreakGlassExport

open CedarPooSpec.ClinicalBreakGlassExample

def manifest : Except String Lean.Json := do
  let integrated ← cases.mapM fun (name, req, _) =>
    CedarPooSpec.ClinicalBreakGlassExample.program.authorizationCase name "clinical-integrated" "Integrated" req entities
  let before ← CedarPooSpec.ClinicalBreakGlassExample.program.authorizationCase
      "pre-integration-broad-permit" "clinical-emergency" "Emergency" (request remoteRecord {}) entities
  let preference ← CedarPooSpec.ClinicalBreakGlassExample.program.authorizationCase
      "preference-released" "clinical-integrated" "Integrated" (request restrictedRecord {}) unrestrictedEntities
  return Lean.Json.mkObj [("cases", Lean.toJson (before :: integrated ++ [preference]))]

end CedarPooSpec.ClinicalBreakGlassExport
