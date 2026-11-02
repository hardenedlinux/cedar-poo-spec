import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Vehicle.Uptane.SupplierTransition

/-! Export the same policy revisions and per-layer requests checked in Lean. -/

namespace CedarPooSpec.SupplierTransitionExport

open CedarPooSpec.SupplierTransitionExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.SupplierTransitionExample.model CedarPooSpec.SupplierTransitionExample.schema :=
      CedarPooSpec.SupplierTransitionExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, root, supplier, target, facts, _, _) in updateCases do
    for ((layerRoot, request), index) in (updateChecks root supplier target facts).zipIdx do
      let receipt ← owner.case
          s!"{name}-layer-{index}" layerRoot.toLower layerRoot request entities
      rows := rows ++ [receipt]
  for (name, root, target, facts, _) in manifestCases do
    let receipt ← owner.case
        name root.toLower root (manifestRequest target facts) entities
    rows := rows ++ [receipt]
  return { cases := rows }

end CedarPooSpec.SupplierTransitionExport
