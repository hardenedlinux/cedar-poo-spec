import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Vehicle.Mission.SuccessorBoundary

/-!
One controlled maintenance change: a fallback handoff now requires the
route-approved context fact. The six roots inherit one Base edit. Direct
Cedar snapshots for the same change live in DirectChangePolicies/.
-/

namespace CedarPooSpec.MaintenanceComparisonExample

open CedarPooSpec.SuccessorBoundaryExample CedarPooSpec.PolicyModules

def guardedFallback : Cedar.Spec.Policy :=
  { safeFallback with condition := [
      { kind := .when, body := ctx "routeApproved" }] }

def changedModel : Model :=
  { model with modules := model.modules.map fun module =>
      if module.name == "Base" then
        { module with edits := [.extend nominal, .extend guardedFallback] }
      else module }

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def changedProgram : CedarPooSpec.Functional.Program changedModel CedarPooSpec.SuccessorBoundaryExample.schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    changedModel CedarPooSpec.SuccessorBoundaryExample.schema (changedModel.modules.map (·.name)) (by native_decide)

def deniedFallback : Candidate := { routeApproved := false }
def roots : List String :=
  ["Base", "Platform", "Mission", "Evidence", "Integrated", "Current"]

def changedAllows
     (root : String) (candidate : Candidate)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MaintenanceComparisonExample.changedModel CedarPooSpec.SuccessorBoundaryExample.schema :=
      CedarPooSpec.MaintenanceComparisonExample.changedProgram) : Bool :=
  match programContext.authorizeLayers
      [(root, request fallback candidate)] entities with
  | .error _ => false
  | .ok receipts => CedarPooSpec.Authorization.Compound.layersAllowed receipts

theorem oneOwnerEditChangesEveryRevision :
    roots.length = 6 ∧
    roots.all (fun root =>
      authorized root fallback deniedFallback &&
      !changedAllows root deniedFallback &&
      changedAllows root clear) = true := by
  native_decide

def manifest
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MaintenanceComparisonExample.changedModel CedarPooSpec.SuccessorBoundaryExample.schema :=
      CedarPooSpec.MaintenanceComparisonExample.changedProgram) : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for root in roots do
    let receipt ← programContext.authorizationCase
        s!"fallback-route-{root.toLower}" root.toLower root (request fallback deniedFallback) entities
    rows := rows ++ [receipt]
    let receipt ← programContext.authorizationCase
        s!"fallback-clear-{root.toLower}" root.toLower root (request fallback clear) entities
    rows := rows ++ [receipt]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.MaintenanceComparisonExample

def main : IO Unit := do
  match CedarPooSpec.MaintenanceComparisonExample.manifest with
  | .ok value => IO.println value.compress
  | .error error => throw (IO.userError error)
