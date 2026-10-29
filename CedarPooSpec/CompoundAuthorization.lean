import CedarPooSpec.PolicyPreparation
import Cedar.Spec.Authorizer
import LeanPoo.Functional.Assembly

/-!
Compound authorization evaluates several Cedar requests against one compiled
POO root and one caller-supplied entity snapshot. The caller remains
responsible for atomic business execution and authentic input facts.
-/

namespace CedarPooSpec.CompoundAuthorization

open Cedar.Spec CedarPooSpec.PolicyModules

/-- A compound receipt binds all responses to one exact POO compilation. -/
structure Receipt (model : Model) (root : String) (requests : List Request)
    (entities : Entities) where
  policies : Policies
  compiled : model.compile root = .ok policies
  responses : List Response
  evaluated : responses = requests.map (fun req => isAuthorized req entities policies)

/-- Every query must allow, and no query may have a policy evaluation error. -/
def Receipt.allowed {model : Model} {root : String} {requests : List Request}
    {entities : Entities} (receipt : Receipt model root requests entities) : Bool :=
  !requests.isEmpty &&
    receipt.responses.all (fun response =>
      response.decision == .allow && response.erroringPolicies.isEmpty)

/-- Extract the actual response from a proof-indexed singleton receipt. -/
def Receipt.singleResponse (receipt : Receipt model root [request] entities) : Response :=
  receipt.responses[0]'(by rw [receipt.evaluated]; simp)

theorem Receipt.singleResponse_evaluated (receipt : Receipt model root [request] entities) :
    receipt.singleResponse = isAuthorized request entities receipt.policies := by
  simp [Receipt.singleResponse, receipt.evaluated]

abbrev Compiler (model : Model) := LeanPoo.Functional.Factory String
  (fun root => Except PolicyModules.Error (PolicyPreparation.Compiled model root))

def ofCompiled (compiled : PolicyPreparation.Compiled model root)
    (requests : List Request) (entities : Entities) : Receipt model root requests entities :=
  ⟨compiled.policies, compiled.compiled,
    requests.map (fun req => isAuthorized req entities compiled.policies), rfl⟩

def authorizeAllWith (compiler : Compiler model) (root : String) (requests : List Request)
    (entities : Entities) : Except PolicyModules.Error (Receipt model root requests entities) :=
  (compiler root).map fun compiled => ofCompiled compiled requests entities

/-- The compile-only public entrypoint retains its existing error boundary. -/
def authorizeAll (model : Model) (root : String) (requests : List Request)
    (entities : Entities) : Except PolicyModules.Error (Receipt model root requests entities) :=
  authorizeAllWith (PolicyPreparation.compile model) root requests entities

/-- One decision from one root, with its exact compilation and Cedar response. -/
structure LayerReceipt (model : Model) (entities : Entities) where
  root : String
  request : Request
  policies : Policies
  compiled : model.compile root = .ok policies
  response : Response
  evaluated : response = isAuthorized request entities policies

/-- All required layers must allow without policy evaluation errors. -/
def layersAllowed {model : Model} {entities : Entities}
    (receipts : List (LayerReceipt model entities)) : Bool :=
  !receipts.isEmpty && receipts.all fun layer =>
    layer.response.decision == .allow && layer.response.erroringPolicies.isEmpty

/-- One exact compilation can serve several requests against the same root. -/
structure CompiledRoot (model : Model) where
  root : String
  policies : Policies
  compiled : model.compile root = .ok policies

private abbrev RootCompilation (model : Model) (root : String) :=
  PolicyPreparation.Compiled model root

private def cachedCompilation? (model : Model) (cache : List (CompiledRoot model))
    (root : String) : Option (RootCompilation model root) :=
  match cache with
  | [] => none
  | entry :: rest =>
      if h : entry.root = root then
        some ⟨entry.policies, by cases h; exact entry.compiled⟩
      else
        cachedCompilation? model rest root

private def getCompilation (model : Model) (compiler : Compiler model) (cache : List (CompiledRoot model))
    (root : String) : Except PolicyModules.Error
      (RootCompilation model root × List (CompiledRoot model)) :=
  match cachedCompilation? model cache root with
  | some result => .ok (result, cache)
  | none =>
      match compiler root with
      | .error error => .error error
      | .ok compiled =>
          .ok (compiled, ⟨root, compiled.policies, compiled.compiled⟩ :: cache)

/-- Evaluate layers in order; compile each distinct POO root at most once. -/
def authorizeLayersWith (compiler : Compiler model) (checks : List (String × Request))
    (entities : Entities) : Except PolicyModules.Error (List (LayerReceipt model entities)) :=
  go checks []
where
  go (remaining : List (String × Request)) (cache : List (CompiledRoot model)) :
      Except PolicyModules.Error (List (LayerReceipt model entities)) := do
    match remaining with
    | [] => return []
    | (root, request) :: rest =>
        let (⟨policies, hc⟩, updated) ← getCompilation model compiler cache root
        let tail ← go rest updated
        return ⟨root, request, policies, hc,
          isAuthorized request entities policies, rfl⟩ :: tail

def authorizeLayers (model : Model) (checks : List (String × Request))
    (entities : Entities) : Except PolicyModules.Error (List (LayerReceipt model entities)) :=
  authorizeLayersWith (PolicyPreparation.compile model) checks entities

end CedarPooSpec.CompoundAuthorization
