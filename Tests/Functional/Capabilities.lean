import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Payment.PaymentReleaseExport
import Examples.Health.PriorAuthorization.InternalChannelsExport
import Examples.Health.PriorAuthorization.ValidatedExport
import Tests.Language.SchemaProjection

namespace CedarPooSpec.FunctionalCapabilitiesTest

open Cedar.Spec Cedar.Validation CedarPooSpec.Functional

theorem fold_constants {Context Input Acc : Type}
    (combine : Context → Acc → Input → Acc)
    (seed : LeanPoo.Functional.Factory Context (fun _ => Acc))
    (items : List Input) (context : Context) :
    LeanPoo.Functional.Factory.fold combine seed (items.map fun item _ => item) context =
      items.foldl (combine context) (seed context) := by
  simp [LeanPoo.Functional.Factory.fold, List.foldl_map]

/-- Independent pre-refactor publication algorithm, including error order. -/
private def referencePublish (model : PolicyModules.Model) (root : String) (schema : Schema) :
    Except PolicyJson.PublicationError (PolicyJson.Publication model root schema) :=
  match hc : model.compile root with
  | .error error => .error (.composition error)
  | .ok policies =>
    match ha : SchemaAdmission.validateDefinitions schema with
    | .error error => .error (.schema error)
    | .ok () =>
      match hs : schema.validateWellFormed with
      | .error error => .error (.schema error)
      | .ok () =>
        match hv : Cedar.Validation.validate policies schema with
        | .error error => .error (.policy error)
        | .ok () =>
          match hj : PolicyJson.policySet policies with
          | .error error => .error (.export error)
          | .ok json =>
            if unique : (policies.map Policy.id).Nodup then
              .ok {
                policies
                compiled := hc
                schemaDefinitionsValid := ha
                schemaValid := hs
                policyValid := hv
                idsUnique := unique
                json
                serialized := hj, snapshot := Transport.SourceSnapshot.ofJson json, snapshot_value := rfl }
            else .error .duplicatePolicyIds

/-- All inputs, including multi-error inputs, preserve the complete result. -/
theorem publication_exact (model : PolicyModules.Model) (root : String) (schema : Schema) :
    PolicyJson.publish model root schema = referencePublish model root schema := by
  unfold referencePublish
  symm
  split
  next error hc =>
    rw [PolicyJson.publish, PolicyPreparation.compile_error hc]
    rfl
  next policies hc =>
    rw [PolicyJson.publish, PolicyPreparation.compile_ok hc]
    simp only [Except.mapError, bind, Except.bind]
    split
    next error ha =>
      rw [PolicyPreparation.check_definitions_error _ _ _ ha]
    next ha =>
      split
      next error hs =>
        rw [PolicyPreparation.check_schema_error _ _ _ ha hs]
      next hs =>
        split
        next error hv =>
          rw [PolicyPreparation.check_policy_error _ _ _ ha hs hv]
        next hv =>
          rw [PolicyPreparation.check_ok _ _ _ ha hs hv]
          rfl

def noPublish : Operations := fun key =>
  if key == .publish then none else cedar key

example : (match prepare noPublish with
    | .error .publish => true
    | _ => false) = true := by native_decide

-- Missing operations are refused before any malformed context is built.
example : (match prepareProgram noPublish { modules := [] } ⟨Cedar.Data.Map.empty, Cedar.Data.Map.empty⟩
    ["Missing"] with
    | .error (.missingCapability .publish) => true
    | _ => false) = true := by native_decide

def overrideGraph : LeanPoo.C4.Graph := { nodes := [
  { name := "Cedar" }, { name := "Industry", parentOrders := [["Cedar"]] }] }

def overrideOrder : LeanPoo.C4.VerifiedOrder overrideGraph "Industry" :=
  (LeanPoo.C4.linearizeVerified overrideGraph "Industry").toOption.get (by native_decide)

def rejectingCompile : Operations
  | .compile => some fun _ => .error (.composition (.missingModule "industry-contract"))
  | _ => none

def overridden : Operations := assemble overrideOrder fun name =>
  if name == "Industry" then rejectingCompile else if name == "Cedar" then cedar else fun _ => none

example : (prepare overridden).isOk = true := by native_decide
example : (match prepareProgram overridden { modules := [] } ⟨Cedar.Data.Map.empty, Cedar.Data.Map.empty⟩
    ["Root"] with
    | .error (.context "Root" (.composition (.missingModule "industry-contract"))) => true
    | _ => false) = true := by native_decide

example : (match prepareProgram standard { modules := [] } ⟨Cedar.Data.Map.empty, Cedar.Data.Map.empty⟩
    ["first", "second"] with
    | .error (.context "first" _) => true
    | _ => false) = true := by native_decide

def refusingPublisher : Operations
  | .publish => some fun _ _ => .error (.export .unsupportedValue)
  | key => cedar key

namespace Payment
open CedarPooSpec.PaymentReleaseExample

-- Deliberately injected export refusal must not evaluate during authorization.
def withoutExport : Program model schema :=
  (prepareProgram refusingPublisher model schema ["Integrated"]).toOption.get (by native_decide)

example : (withoutExport.authorize "Integrated" [request bob release small] entities).toOption.map
    (·.allowed) = some true ∧ (withoutExport.publish "Integrated").isOk = false := by native_decide

example : (program.authorize "unknown" [request bob release small] entities).isOk = false := by
  native_decide

example : (program.authorize "Integrated" [] entities).toOption.map (·.allowed) = some false := by
  native_decide

def legacyAuthorized (root : String) (req : Request) : Bool :=
  match model.compile root with
  | .error _ => false
  | .ok policies =>
      let response := isAuthorized req entities policies
      response.decision == .allow && response.erroringPolicies.isEmpty

example : branchCases.all (fun (_, root, principal, action, resource, _) =>
    authorized root principal action resource == legacyAuthorized root (request principal action resource)) =
    true := by native_decide

example : operationCases.all (fun (_, root, preparer, releaser, resource, _) =>
    releaseOperation root preparer releaser resource ==
      (match Authorization.Compound.authorizeAll model root
        [request preparer prepare resource, request releaser release resource] entities with
      | .error _ => false
      | .ok receipt => receipt.allowed)) = true := by native_decide

example : roots.all (fun root =>
    (program.publish root).toOption.map (·.json) ==
      (PolicyJson.publish model root schema).toOption.map (·.json)) = true := by native_decide

-- Duplicate preparation requests retain one immutable root snapshot.
example : (prepareProgram standard model schema ["Integrated", "Integrated"]).toOption.map
    (fun program => program.entries.length) = some 1 := by native_decide

example : (prepareProgram standard model CedarPooSpec.SchemaProjectionTest.danglingAncestorSchema
    ["Integrated"]).isOk = false := by native_decide

def changedEntities : Entities := Cedar.Data.Map.make (entities.toList.map fun (uid, data) =>
  (uid, if uid == bob then emptyData [] else data))

example : (program.authorize "Integrated" [request bob release small] entities).toOption.map
    (·.allowed) = some true ∧
    (program.authorize "Integrated" [request bob release small] changedEntities).toOption.map
    (·.allowed) = some false := by native_decide

def revisedModel : PolicyModules.Model := { model with modules := model.modules.map fun item =>
  if item.name == "Threshold" then
    { item with edits := [.overlay ({ controllerTemplate with threshold := "1000.0000" } :
        CedarPooSpec.Vertical.FinancialServices.ControllerRelease).bounded] }
  else item }

def revisedProgram : Program revisedModel schema :=
  (prepareProgram standard revisedModel schema ["Integrated"]).toOption.get (by native_decide)

example : (program.authorize "Integrated" [request bob release large] entities).toOption.map
    (·.allowed) = some false ∧
    (revisedProgram.authorize "Integrated" [request bob release large] entities).toOption.map
    (·.allowed) = some true ∧
    (program.authorize "Integrated" [request bob release large] entities).toOption.map
    (·.allowed) = some false := by native_decide

def referenceManifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, root, preparer, releaser, resource, _) in operationCases do
    let first ← PolicyJson.authorizationCase s!"{name}-prepare" root.toLower model root
      (request preparer prepare resource) entities
    let second ← PolicyJson.authorizationCase s!"{name}-release" root.toLower model root
      (request releaser release resource) entities
    rows := rows ++ [first, second]
  for (name, root, principal, action, resource, _) in branchCases do
    let row ← PolicyJson.authorizationCase name root.toLower model root
      (request principal action resource) entities
    rows := rows ++ [row]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

example : (CedarPooSpec.PaymentReleaseExport.manifest.bind (·.toJson)).toOption.map (·.compress) =
    referenceManifest.toOption.map (·.compress) := by native_decide

end Payment

namespace Medical
open CedarPooSpec.PriorAuthorizationInternalChannels

def legacyAdmitted (root : String) (input : Envelope) : Bool :=
  match model.compile root with
  | .error _ => false
  | .ok policies =>
      let response := isAuthorized (request input) entities policies
      response.decision == .allow && response.erroringPolicies.isEmpty

example : cases.all (fun (_, root, input, _) =>
    admitted root input == legacyAdmitted root input) = true := by native_decide

example : (syntheticDelivery "ChannelGoverned" token).2 = [.verificationToken] ∧
    (syntheticDelivery "ChannelGoverned" chart).2 = [] ∧
    (syntheticDelivery "MemoryRemoved" handle).2 = [] := by native_decide

example : roots.all (fun root =>
    (program.publish root).toOption.map (·.json) ==
      (PolicyJson.publish model root schema).toOption.map (·.json)) = true := by native_decide

-- Open-root compatibility includes valid roots not in the retained hot set.
example : model.modules.all (fun item => cases.all (fun (_, _, input, _) =>
    admitted item.name input == legacyAdmitted item.name input)) = true := by native_decide

def referenceManifest : Except String Lean.Json := do
  let rows ← cases.mapM fun (name, root, input, _) =>
    PolicyJson.authorizationCase name root model root (request input) entities
  SchemaJson.validatedManifest schema rows

example : (CedarPooSpec.PriorAuthorizationInternalChannelsExport.manifest.bind (·.toJson)).toOption.map (·.compress) =
    referenceManifest.toOption.map (·.compress) := by native_decide

end Medical

namespace PriorAuthorization
open CedarPooSpec.PriorAuthorizationExample

private def referenceReplay (root : String) (initial : State) (attempts : List Attempt) :
    List (Request × Bool) × State :=
  let (state, rows) := attempts.foldl (fun (state, rows) attempt =>
    let req := request state attempt
    let allowed := authorized root state attempt
    (if allowed then advance state attempt else state, rows ++ [(req, allowed)])) (initial, [])
  (rows, state)

theorem replay_exact (root : String) (initial : State) (attempts : List Attempt) :
    replay root initial attempts = referenceReplay root initial attempts := by
  simp only [replay, replayFactory, referenceReplay, fold_constants]

def legacyAuthorized (root : String) (state : State) (attempt : Attempt) : Bool :=
  match model.compile root with
  | .error _ => false
  | .ok policies =>
      let response := isAuthorized (request state attempt) entities policies
      response.decision == .allow && response.erroringPolicies.isEmpty

def legacyReplay (root : String) (initial : State) (attempts : List Attempt) :
    List (Request × Bool) × State :=
  let (state, rows) := attempts.foldl (fun (state, rows) attempt =>
    let req := request state attempt
    let allowed := legacyAuthorized root state attempt
    (if allowed then advance state attempt else state, rows ++ [(req, allowed)])) (initial, [])
  (rows, state)

example : cases.all (fun (_, root, state, attempts, _) =>
    (replay root state attempts).1 == (legacyReplay root state attempts).1 &&
    (replay root state attempts).2.clinicalSeen == (legacyReplay root state attempts).2.clinicalSeen &&
    (replay root state attempts).2.billingSeen == (legacyReplay root state attempts).2.billingSeen) =
    true := by native_decide

def referenceManifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, root, state, attempts, _) in cases do
    for ((req, _), index) in (legacyReplay root state attempts).1.zipIdx do
      let row ← PolicyJson.authorizationCase s!"{name}-step-{index}" root model root req entities
      rows := rows ++ [row]
  SchemaJson.validatedManifest schema rows

example : (CedarPooSpec.PriorAuthorizationValidatedExport.manifest.bind (·.toJson)).toOption.map (·.compress) =
    referenceManifest.toOption.map (·.compress) := by native_decide

def malformedReference : Except String Lean.Json := do
  let row ← PolicyJson.authorizationCase "missing-disclosure-fact" "Governed" model "Governed"
    missingDisclosureFact entities
  return Lean.Json.mkObj [("cases", Lean.toJson [row])]

example : (CedarPooSpec.PriorAuthorizationValidatedExport.malformedManifest.bind (·.toJson)).toOption.map (·.compress) =
    malformedReference.toOption.map (·.compress) := by native_decide

end PriorAuthorization

end CedarPooSpec.FunctionalCapabilitiesTest

open Lean Elab Command

-- Universal API/Contract proofs must not acquire fixture-native or sorry axioms.
run_cmd do
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  for declaration in [
      ``CedarPooSpec.FunctionalCapabilitiesTest.publication_exact,
      ``CedarPooSpec.FunctionalCapabilitiesTest.fold_constants,
      ``CedarPooSpec.Functional.coherent,
      ``CedarPooSpec.Functional.Ready.allowed_eq,
      ``CedarPooSpec.Vertical.Health.DisclosureProfile.policy_requires_contract,
      ``CedarPooSpec.Vertical.FinancialServices.ControllerReleaseProfile.policy_requires_contract] do
    let dependencies ← collectAxioms declaration
    for dependency in dependencies do
      unless allowed.contains dependency.toString do
        throwError "Functional Cedar axiom boundary changed: {declaration}: {dependency}"
  logInfo "FUNCTIONAL-CEDAR-AXIOMS-OK six universal API/Contract/workflow proofs"
