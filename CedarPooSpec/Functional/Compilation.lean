import CedarPooSpec.Authorization.Compound

/-! Compile-stage Functional consumers for APIs that have no schema premise.
This reuses the existing compiled evidence, receipt and distinct-root cache. -/
namespace CedarPooSpec.Functional
open Cedar.Spec

abbrev Compilation := Authorization.Compound.Compiler

def compilation (model : PolicyModules.Model) : Compilation model :=
  PolicyPreparation.compile model

def Compilation.authorize (compiler : Compilation model) (root : String)
    (requests : List Request) (entities : Entities) :=
  Authorization.Compound.authorizeAllWith compiler root requests entities

def Compilation.response (compiler : Compilation model) (root : String)
    (request : Request) (entities : Entities) :=
  (compiler.authorize root [request] entities).map (·.singleResponse)

def Compilation.authorizeLayers (compiler : Compilation model)
    (checks : List (String × Request)) (entities : Entities) :=
  Authorization.Compound.authorizeLayersWith compiler checks entities

theorem compilation_authorize (model : PolicyModules.Model) (root : String)
    (requests : List Request) (entities : Entities) :
    (compilation model).authorize root requests entities =
      Authorization.Compound.authorizeAll model root requests entities := rfl

theorem compilation_layers (model : PolicyModules.Model) (checks : List (String × Request))
    (entities : Entities) :
    (compilation model).authorizeLayers checks entities =
      Authorization.Compound.authorizeLayers model checks entities := rfl

end CedarPooSpec.Functional
