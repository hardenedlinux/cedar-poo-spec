import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Vehicle.Uptane.SupplierTransition

/-! Export the same policy revisions and per-layer requests checked in Lean. -/

namespace CedarPooSpec.SupplierTransitionExport

open CedarPooSpec.SupplierTransitionExample

def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, root, supplier, target, facts, _, _) in updateCases do
    for ((layerRoot, request), index) in (updateChecks root supplier target facts).zipIdx do
      let receipt ← CedarPooSpec.SupplierTransitionExample.program.authorizationCase
          s!"{name}-layer-{index}" layerRoot.toLower layerRoot request entities
      rows := rows ++ [receipt]
  for (name, root, target, facts, _) in manifestCases do
    let receipt ← CedarPooSpec.SupplierTransitionExample.program.authorizationCase
        name root.toLower root (manifestRequest target facts) entities
    rows := rows ++ [receipt]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.SupplierTransitionExport
