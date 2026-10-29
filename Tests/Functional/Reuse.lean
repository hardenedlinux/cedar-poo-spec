import CedarPooSpec.Functional.Reuse
import Tests.Functional.RootFamilies
import Tests.Functional.Effectful

namespace CedarPooSpec.FunctionalReuseTest
open Cedar.Spec CedarPooSpec.Functional
namespace Cross
open CedarPooSpec.CrossAgentEgressExample

def cold : Program model schema :=
  (prepareProgram standard model schema []).toOption.get (by native_decide)

def refused : Program model schema :=
  (prepareProgram FunctionalCapabilitiesTest.refusingPublisher model schema []).toOption.get
    (by native_decide)

def changed : Program reloadedModel schema :=
  (prepareProgram standard reloadedModel schema []).toOption.get (by native_decide)

def invalidSchema : Program model SchemaProjectionTest.danglingAncestorSchema :=
  (prepareProgram standard model SchemaProjectionTest.danglingAncestorSchema []).toOption.get
    (by native_decide)

example : RootSlot invalidSchema := by
  fail_if_success exact RootSlot.empty cold
  exact RootSlot.empty invalidSchema
example : (match (RootSlot.read (RootSlot.empty invalidSchema) "CrossAgentGoverned").1 with
  | .error (.context _ (.schema _)) => true
  | _ => false) = true := by native_decide

example : RootSlot changed := by
  fail_if_success exact RootSlot.empty cold
  exact RootSlot.empty changed
example : RootSlot refused := by
  fail_if_success exact RootSlot.empty cold
  exact RootSlot.empty refused

example : (let first := RootSlot.read (RootSlot.empty cold) "CrossAgentGoverned"
           let again := RootSlot.read first.2.1 "CrossAgentGoverned"
           let other := RootSlot.read again.2.1 "CrossAgentIncident"
           let evicted := RootSlot.read other.2.1 "CrossAgentGoverned"
           (!first.2.2 && again.2.2 && !other.2.2 && !evicted.2.2 &&
             evicted.2.1.retained.toList.length == 1)) = true := by native_decide

example : (let first := RootSlot.read (RootSlot.empty cold) "absent"
           let again := RootSlot.read first.2.1 "absent"
           match again.1 with
           | .error (.context root (.composition _)) => again.2.2 && root == "absent"
           | _ => false) = true := by native_decide

-- Same cached preparation, current requests still change actual decisions.
example : (let first := RootSlot.read (RootSlot.empty cold) "CrossAgentGoverned"
           let again := RootSlot.read first.2.1 "CrossAgentGoverned"
           match again.1 with
           | .error _ => false
           | .ok ready =>
             again.2.2 &&
             (ready.authorize [request .delegationShared {} sendA] entities).allowed &&
             !(ready.authorize [request .delegationShared
               { budget := { sharedUsed := 1 } } sendA] entities).allowed &&
             decide ((ready.authorize [request .delegationShared {} sendA] Cedar.Data.Map.empty).responses =
               [isAuthorized (request .delegationShared {} sendA) Cedar.Data.Map.empty ready.checked.policies])) = true := by native_decide

example : (let result := RootSlot.read (RootSlot.empty refused) "CrossAgentGoverned"
           match result.1 with
           | .error _ => false
           | .ok ready =>
             (ready.authorize [request .delegationShared {} sendA] entities).allowed &&
             !ready.publish.get.isOk) = true := by native_decide

-- Old and new model scopes stay separate even though their root labels agree.
example : (let old := RootSlot.read (RootSlot.empty cold) "CrossAgentGoverned"
           let fresh := RootSlot.read (RootSlot.empty changed) "CrossAgentGoverned"
           match old.1, fresh.1 with
           | .ok before, .ok after =>
             (before.authorize [request .delegationShared {} sendB] entities).allowed &&
             !(after.authorize [request .delegationShared {} sendB] entities).allowed
           | _, _ => false) = true := by native_decide

example : (match cold.authorizationCases [
    ⟨"first", "v1", "missing-first", request .delegationShared {} sendA, entities⟩,
    ⟨"second", "v1", "missing-second", request .delegationShared {} sendA, entities⟩] with
  | .error message => message == "Cedar root missing-first: POO composition failed"
  | .ok _ => false) = true := by native_decide

end Cross

namespace Payment
open CedarPooSpec.PaymentReleaseExample

def source : Program model schema :=
  (prepareProgram standard model schema []).toOption.get (by native_decide)

example : (let first := RootSlot.read (RootSlot.empty source) "Integrated"
           let again := RootSlot.read first.2.1 "Integrated"
           match again.1 with
           | .error _ => false
           | .ok ready =>
             again.2.2 && (ready.authorize [request bob release small] entities).allowed &&
             !(ready.authorize [request bob release small]
               FunctionalCapabilitiesTest.Payment.changedEntities).allowed) = true := by native_decide
end Payment

-- These compare final bytes against independent pre-migration algorithms.
example : PriorAuthorizationValidatedExport.manifest.map Lean.Json.compress =
    FunctionalCapabilitiesTest.PriorAuthorization.referenceManifest.map Lean.Json.compress := by
  native_decide
example : CrossAgentEgressValidatedExport.manifest.map Lean.Json.compress =
    EffectfulCapabilitiesTest.Reference.CrossExport.manifest.map Lean.Json.compress := by native_decide

open Lean in
run_cmd do
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  for declaration in [``CedarPooSpec.Functional.RootSlot.read_value,
      ``CedarPooSpec.Functional.RootSlot.bound,
      ``CedarPooSpec.Functional.RootSlot.read_hit,
      ``CedarPooSpec.Functional.Program.authorizationCasesFrom_eq,
      ``CedarPooSpec.Functional.Program.authorizationCases_eq] do
    let dependencies ← collectAxioms declaration
    for dependency in dependencies do
      unless allowed.contains dependency.toString do
        throwError "Functional reuse axiom boundary changed: {declaration}: {dependency}"
  logInfo "FUNCTIONAL-CEDAR-REUSE-AXIOMS-OK five universal value/hit/bound/batch proofs"
end CedarPooSpec.FunctionalReuseTest
