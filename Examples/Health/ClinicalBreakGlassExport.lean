import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import Examples.Health.ClinicalBreakGlass

/-! Export clinical POO revisions and Lean-computed authorization receipts. -/

namespace CedarPooSpec.ClinicalBreakGlassExport

open CedarPooSpec.ClinicalBreakGlassExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.ClinicalBreakGlassExample.model CedarPooSpec.ClinicalBreakGlassExample.schema :=
      CedarPooSpec.ClinicalBreakGlassExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let integrated ← cases.mapM fun (name, req, _) =>
    owner.case name "clinical-integrated" "Integrated" req entities
  let before ← owner.case
      "pre-integration-broad-permit" "clinical-emergency" "Emergency" (request remoteRecord {}) entities
  let preference ← owner.case
      "preference-released" "clinical-integrated" "Integrated" (request restrictedRecord {}) unrestrictedEntities
  return { cases := (before :: integrated ++ [preference]) }

end CedarPooSpec.ClinicalBreakGlassExport
