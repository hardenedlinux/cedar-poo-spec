import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import Examples.Health.ClinicalBreakGlass

/-! Export clinical POO revisions and Lean-computed authorization receipts. -/

namespace CedarPooSpec.ClinicalBreakGlassExport

open CedarPooSpec.ClinicalBreakGlassExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let integrated ← cases.mapM fun (name, req, _) =>
    CedarPooSpec.ClinicalBreakGlassExample.program.case name "clinical-integrated" "Integrated" req entities
  let before ← CedarPooSpec.ClinicalBreakGlassExample.program.case
      "pre-integration-broad-permit" "clinical-emergency" "Emergency" (request remoteRecord {}) entities
  let preference ← CedarPooSpec.ClinicalBreakGlassExample.program.case
      "preference-released" "clinical-integrated" "Integrated" (request restrictedRecord {}) unrestrictedEntities
  return { cases := (before :: integrated ++ [preference]) }

end CedarPooSpec.ClinicalBreakGlassExport
