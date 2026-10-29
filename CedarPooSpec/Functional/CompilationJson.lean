import CedarPooSpec.Functional.Compilation
import CedarPooSpec.PolicyJson

/-! Compile-stage JSON projection without adding schema admission. -/
namespace CedarPooSpec.Functional
open Cedar.Spec

def Compilation.export (compiler : Compilation model) (root : String) :
    Except (Sum PolicyModules.Error PolicyJson.Error) Lean.Json := do
  let compiled ← (compiler root).mapError Sum.inl
  (PolicyJson.policySet compiled.policies).mapError Sum.inr

def Compilation.authorizationCase (compiler : Compilation model)
    (name revision root : String) (request : Request) (entities : Entities) : Except String Lean.Json := do
  let compiled ← (compiler root).mapError reprStr
  PolicyJson.authorizationCaseCompiled compiled name revision request entities

theorem compilation_export (model : PolicyModules.Model) (name revision root : String)
    (request : Request) (entities : Entities) :
    (compilation model).authorizationCase name revision root request entities =
      PolicyJson.authorizationCase name revision model root request entities := rfl
end CedarPooSpec.Functional
