import CedarPooSpec.Functional.Compilation
import CedarPooSpec.Transport.Case

/-! Compile-stage JSON projection without adding schema admission. -/
namespace CedarPooSpec.Functional
open Cedar.Spec

def Compilation.export (compiler : Compilation model) (root : String) :
    Except (Sum PolicyModules.Error PolicyJson.Error) Lean.Json := do
  let compiled ← (compiler.compile root).mapError Sum.inl
  (PolicyJson.policySet compiled.policies).mapError Sum.inr

def Compilation.authorizationCase (compiler : Compilation model)
    (name revision root : String) (request : Request) (entities : Entities) : Except String Lean.Json := do
  let compiled ← (compiler.compile root).mapError reprStr
  PolicyJson.authorizationCaseCompiled compiled name revision request entities

theorem compilation_export (model : PolicyModules.Model) (name revision root : String)
    (request : Request) (entities : Entities) :
    (compilation model).authorizationCase name revision root request entities =
      PolicyJson.authorizationCase name revision model root request entities := by
  unfold Compilation.authorizationCase
  rw [compilation_eq]
  rfl
/-- Typed compile-stage case; only the policy source is projected here. -/
def Compilation.case (compiler : Compilation model)
    (name revision root : String) (request : Request) (entities : Entities) :
    Except String Transport.Case := do
  let compiled ← (compiler.compile root).mapError reprStr
  match h : PolicyJson.policySet compiled.policies with
  | .error error => .error (reprStr error)
  | .ok json => .ok {
      name, revision
      policy := { policies := compiled.policies, snapshot := Transport.SourceSnapshot.ofJson json, aligned := h }
      request, entities
      response := Thunk.mk fun _ => isAuthorized request entities compiled.policies
      evaluated := rfl }

end CedarPooSpec.Functional
