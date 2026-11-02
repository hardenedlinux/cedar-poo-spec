import CedarPooSpec.Authorization.Compound

/-! Compile-stage Functional consumers for APIs that have no schema premise.
This reuses the existing compiled evidence, receipt and distinct-root cache. -/
namespace CedarPooSpec.Functional
open Cedar.Spec

/-- A compile-stage owner retains actual graph preparation as data. A bare
curried function lets compiler eta expansion reconstruct it for every root. -/
structure Compilation (model : PolicyModules.Model) where
  prepared : Thunk (LeanPoo.C4.Prepared model.graph)
  resolve : LeanPoo.C4.Prepared model.graph → Authorization.Compound.Compiler model

def Compilation.compile (compiler : Compilation model) (root : String) :=
  compiler.resolve compiler.prepared.get root

def compilation (model : PolicyModules.Model) : Compilation model :=
  ⟨Thunk.mk (fun _ => model.prepareC4), PolicyPreparation.compilePrepared model⟩

theorem compilation_eq (model : PolicyModules.Model) :
    (compilation model).compile = PolicyPreparation.compile model := by
  funext root
  exact PolicyPreparation.compilePrepared_eq model _ root

def Compilation.authorize (compiler : Compilation model) (root : String)
    (requests : List Request) (entities : Entities) :=
  Authorization.Compound.authorizeAllWith compiler.compile root requests entities

def Compilation.response (compiler : Compilation model) (root : String)
    (request : Request) (entities : Entities) :=
  (compiler.authorize root [request] entities).map (·.singleResponse)

def Compilation.authorizeLayers (compiler : Compilation model)
    (checks : List (String × Request)) (entities : Entities) :=
  Authorization.Compound.authorizeLayersWith compiler.compile checks entities

theorem compilation_authorize (model : PolicyModules.Model) (root : String)
    (requests : List Request) (entities : Entities) :
    (compilation model).authorize root requests entities =
      Authorization.Compound.authorizeAll model root requests entities := by
  unfold Compilation.authorize
  rw [compilation_eq]
  rfl

theorem compilation_layers (model : PolicyModules.Model) (checks : List (String × Request))
    (entities : Entities) :
    (compilation model).authorizeLayers checks entities =
      Authorization.Compound.authorizeLayers model checks entities := by
  unfold Compilation.authorizeLayers
  rw [compilation_eq]
  rfl

end CedarPooSpec.Functional
