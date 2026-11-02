import CedarPooSpec.Functional.Compilation
import CedarPooSpec.Authorization.Delta.Model
import CedarPooSpec.Authorization.Compound

/-!
A finite authorization delta for an operation that requires several Cedar
decisions. The caller supplies the same ordered requests on both sides and
authenticates both entity snapshots. Different POO roots may implement the
two revisions, but changing the operation topology is a separate review.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec Cedar.Validation CedarPooSpec.PolicyModules

/-- One required check, including the roots that produced its two decisions. -/
structure CompoundLayerImpact where
  beforeRoot : String
  afterRoot : String
  request : Request
  impact : SnapshotImpact

/-- A complete operation allows only when every required layer allows. -/
structure CompoundImpact where
  layers : List CompoundLayerImpact
  beforeAllowed : Bool
  afterAllowed : Bool

def CompoundImpact.gained (report : CompoundImpact) : Bool :=
  !report.beforeAllowed && report.afterAllowed

def CompoundImpact.lost (report : CompoundImpact) : Bool :=
  report.beforeAllowed && !report.afterAllowed

/-- Compare the same ordered compound operation under two POO revisions and
    authenticated entity snapshots. A missing or changed check is rejected;
    each layer is schema validated and rejects Cedar evaluation errors. -/
def compareCompoundSnapshots (schema : Schema) (model : Model)
    (beforeChecks afterChecks : List (String × Request))
    (beforeEntities afterEntities : Entities) : Except Error CompoundImpact := do
  if beforeChecks.isEmpty then
    throw .operationChanged
  if beforeChecks.map Prod.snd != afterChecks.map Prod.snd then
    throw .operationChanged
  let compiler := CedarPooSpec.Functional.compilation model
  let beforeLayers ← (compiler.authorizeLayers
      beforeChecks beforeEntities).mapError Error.compilation
  let afterLayers ← (compiler.authorizeLayers
      afterChecks afterEntities).mapError Error.compilation
  let layers ← (beforeLayers.zip afterLayers).mapM fun (beforeLayer, afterLayer) => do
    let impact ← compareOperationSnapshots schema beforeLayer.policies afterLayer.policies
      ⟨beforeLayer.request, beforeEntities⟩ ⟨afterLayer.request, afterEntities⟩
    return ⟨beforeLayer.root, afterLayer.root, beforeLayer.request, impact⟩
  return ⟨layers, Authorization.Compound.layersAllowed beforeLayers,
    Authorization.Compound.layersAllowed afterLayers⟩

end CedarPooSpec.Authorization.Delta
