import CedarPooSpec.Functional.CompilationJson
import CedarPooSpec.Functional.Admission
import CedarPooSpec.PolicyProfile
import Examples.Enterprise.AWS.FinancialServices.ClaimSettlementHandoff
import Lean

namespace CedarPooSpec.WholeMigrationTest
open Cedar.Spec CedarPooSpec.PolicyPreparation

/-- Independent original compile-only receipt algorithm, including failures. -/
def referenceAll (model : PolicyModules.Model) (root : String) (requests : List Request)
    (entities : Entities) : Except PolicyModules.Error
      (Authorization.Compound.Receipt model root requests entities) :=
  match h : model.compile root with
  | .error error => .error error
  | .ok policies => .ok ⟨policies, h,
      requests.map (fun request => isAuthorized request entities policies), rfl⟩

theorem compiled_all_exact (model : PolicyModules.Model) (root : String)
    (requests : List Request) (entities : Entities) :
    (Functional.compilation model).authorize root requests entities =
      referenceAll model root requests entities := by
  unfold Functional.Compilation.authorize Functional.compilation Authorization.Compound.authorizeAllWith
  unfold PolicyPreparation.compile referenceAll
  split <;> rename_i first
  all_goals split <;> rename_i second
  all_goals
    have same := first.symm.trans second
    cases same <;> rfl

open AWS.ClaimSettlementHandoff Admission

def forgedHandoff : Handoff.Object :=
  (caseProfile.extendWith "ForgedHandoff" do
    LeanPoo.Object.Dataflow.Builder.value .scope { selected.scope with caseId := "forged" }).toOption.get (by native_decide)
example : Handoff.scope? forgedHandoff = none := by native_decide
example : Handoff.scope? caseProfile = some selected.scope := by native_decide
def emptyHandoff : Handoff.Object :=
  (Handoff.onCase caseProfile "Empty" "" "").toOption.get (by native_decide)
example : (Handoff.scope? emptyHandoff).isNone = true := by native_decide

private def render (setting : String) : Policy := { Policy.allowAll with id := setting }
def policyProfile : PolicyProfile.Object String :=
  (PolicyProfile.define "Owner" "parent" render).toOption.get (by native_decide)
def child : PolicyProfile.Object String :=
  (PolicyProfile.revise policyProfile "Child" "child").toOption.get (by native_decide)
def forgedPolicy : PolicyProfile.Object String :=
  (child.extendWith "Forged" do LeanPoo.Object.Dataflow.Builder.value .policy Policy.allowAll).toOption.get (by native_decide)
example : PolicyProfile.policy? policyProfile = some (render "parent") ∧
    PolicyProfile.policy? child = some (render "child") ∧
    PolicyProfile.policy? forgedPolicy = none := by native_decide

open Lean in
run_cmd do
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  for declaration in [``CedarPooSpec.WholeMigrationTest.compiled_all_exact,
      ``CedarPooSpec.Functional.compilation_layers,
      ``CedarPooSpec.Functional.compilation_export,
      ``CedarPooSpec.Authorization.Compound.Receipt.singleResponse_evaluated,
      ``CedarPooSpec.PolicyProfile.policy_requires_contract,
      ``CedarPooSpec.Admission.Handoff.scope_requires_contract] do
    let axioms ← collectAxioms declaration
    for dependency in axioms do
      unless allowed.contains dependency.toString do
        throwError "Whole migration axiom boundary changed: {declaration}: {dependency}"
  logInfo "WHOLE-FUNCTIONAL-AXIOMS-OK six universal receipt/compilation/Contract proofs"
end CedarPooSpec.WholeMigrationTest
