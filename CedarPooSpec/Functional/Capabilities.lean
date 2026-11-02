import CedarPooSpec.Functional.CompilationJson
import CedarPooSpec.PolicyJson
import CedarPooSpec.Authorization.Compound
import LeanPoo.Functional.CertifiedConsumer
import LeanPoo.Functional.Validation

/-! Select exact Cedar operations once, build checked policy data once per
context, and consume it at current request/entity inputs. -/
namespace CedarPooSpec.Functional

open Cedar.Spec Cedar.Validation
open LeanPoo.Functional
open CedarPooSpec.PolicyPreparation

structure Context where
  model : PolicyModules.Model
  root : String
  schema : Schema

inductive Capability where
  | compile | validate | publish | authorize
  deriving DecidableEq, Repr

abbrev Value (context : Context) : Capability → Type
  | .compile => LeanPoo.C4.Prepared context.model.graph →
      Except PolicyJson.PublicationError (Compiled context.model context.root)
  | .validate => SchemaFacts context.schema → Compiled context.model context.root →
      Except PolicyJson.PublicationError (Validated context.model context.root context.schema)
  | .publish => Validated context.model context.root context.schema →
      Except PolicyJson.PublicationError (PolicyJson.Publication context.model context.root context.schema)
  | .authorize => Validated context.model context.root context.schema →
      (requests : List Request) → (entities : Entities) →
      Authorization.Compound.Receipt context.model context.root requests entities

abbrev Operations := Provider Context Capability Value
abbrev required : List Capability := [.compile, .validate, .publish, .authorize]
abbrev Data (context : Context) := Requirements.Results Value context required

def cedar : Operations
  | .compile => some fun context prepared =>
      (PolicyPreparation.compilePrepared context.model prepared context.root).mapError .composition
  | .validate => some fun _ facts compiled =>
      PolicyPreparation.checkUsing compiled facts
        PolicyJson.PublicationError.schema PolicyJson.PublicationError.policy
  | .publish => some fun _ checked => PolicyJson.publishValidated checked
  | .authorize => some fun _ checked requests entities =>
      Authorization.Compound.ofCompiled checked.toCompiled requests entities

/-- A joint contract over the actual selected authorization function, not a
Boolean assertion about an owner name. Result types also carry Cedar witnesses. -/
def Coherent (context : Context) (data : Data context) : Prop :=
  ∀ (checked : Validated context.model context.root context.schema)
      (requests : List Request) (entities : Entities),
    let receipt := data.2.2.2.1 checked requests entities
    receipt.policies = checked.policies ∧
      receipt.responses = requests.map (fun request =>
        isAuthorized request entities checked.policies)

theorem coherent (context : Context) (data : Data context) : Coherent context data := by
  intro checked requests entities
  let receipt := data.2.2.2.1 checked requests entities
  have same : receipt.policies = checked.policies :=
    Except.ok.inj (receipt.compiled.symm.trans checked.compiled)
  exact ⟨same, by simpa [same] using receipt.evaluated⟩

structure Ready (context : Context) where
  checked : Validated context.model context.root context.schema
  publish : Thunk (Except PolicyJson.PublicationError
    (PolicyJson.Publication context.model context.root context.schema))
  authorize : (requests : List Request) → (entities : Entities) →
    Authorization.Compound.Receipt context.model context.root requests entities
  aligned : ∀ requests entities,
    (authorize requests entities).responses = requests.map (fun request =>
      isAuthorized request entities checked.policies)

theorem Ready.allowed_eq (ready : Ready context) (requests : List Request) (entities : Entities) :
    (ready.authorize requests entities).allowed =
      (!requests.isEmpty && (requests.map (fun request =>
        isAuthorized request entities ready.checked.policies)).all (fun response =>
          response.decision == .allow && response.erroringPolicies.isEmpty)) := by
  simp only [Authorization.Compound.Receipt.allowed, ready.aligned]

/-- Both independent stages must allow without evaluation errors. The shared
checked policy data does not turn one stage's permission into the other's. -/
theorem Ready.allowed_pair (ready : Ready context) (first second : Request) (entities : Entities) :
    (ready.authorize [first, second] entities).allowed =
      ((ready.authorize [first] entities).allowed &&
        (ready.authorize [second] entities).allowed) := by
  simp [Ready.allowed_eq]

def constructUsing (context : Context) (data : Data context) (contract : Coherent context data)
    (prepared : LeanPoo.C4.Prepared context.model.graph)
    (facts : SchemaFacts context.schema) :
    Except PolicyJson.PublicationError (Ready context) := do
  let compiled ← data.1 prepared
  let checked ← data.2.1 facts compiled
  return {
    checked
    publish := Thunk.mk fun _ => data.2.2.1 checked
    authorize := data.2.2.2.1 checked
    aligned := fun requests entities => (contract checked requests entities).2 }

def construct (context : Context) (data : Data context) (contract : Coherent context data) :=
  constructUsing context data contract context.model.prepareC4
    (SchemaFacts.prepare context.schema)

private def prepareWithFacts (provider : Operations) : Except Capability
    (Factory Context (fun context => LeanPoo.C4.Prepared context.model.graph → SchemaFacts context.schema →
      Except PolicyJson.PublicationError (Ready context))) :=
  Requirements.prepareConsumer provider required Coherent
    (fun factories _ context => coherent context (Requirements.build factories context)) constructUsing

/-- Preparation selects factories and certifies their shared evidence contract
before any context is built. Missing capabilities keep the first requested key. -/
def prepare (provider : Operations) : Except Capability
    (Factory Context (fun context => Except PolicyJson.PublicationError (Ready context))) :=
  Requirements.prepareConsumer provider required Coherent
    (fun factories _ context => coherent context (Requirements.build factories context)) construct

theorem prepare_missing (provider : Operations) (key : Capability) :
    prepare provider = .error key ↔ Requirements.prepare provider required = .error key :=
  Requirements.prepareConsumer_error_iff _ _ _ _ _ key

/-- C4 chooses contributed operations; typed results retain their exact Cedar
witnesses even when an operation comes from a different owner. -/
def assemble (order : LeanPoo.C4.VerifiedOrder graph root)
    (providers : String → Operations) : Operations :=
  LeanPoo.Functional.assemble order providers

def graph : LeanPoo.C4.Graph := { nodes := [{ name := "Cedar" }] }

def order : LeanPoo.C4.VerifiedOrder graph "Cedar" :=
  (LeanPoo.C4.linearizeVerified graph "Cedar").toOption.get (by native_decide)

def standard : Operations :=
  assemble order fun name => if name == "Cedar" then cedar else fun _ => none

inductive Error where
  | missingCapability (key : Capability)
  | context (root : String) (cause : PolicyJson.PublicationError)

def Error.message : Error → String
  | .missingCapability key => s!"missing Cedar capability: {repr key}"
  | .context root cause => s!"Cedar root {root}: " ++ match cause with
      | .composition _ => "POO composition failed"
      | .schema _ => "Cedar schema is invalid"
      | .policy _ => "Cedar policy validation failed"
      | .export _ => "Cedar export failed"
      | .duplicatePolicyIds => "Cedar policy IDs are not unique"

/-- Finite retained policy snapshots, indexed by the actual immutable model and
schema. Request/entity data is supplied at each call, never cached as a decision. -/
structure Program (model : PolicyModules.Model) (schema : Schema) where
  retained : Thunk (List ((root : String) × Ready ⟨model, root, schema⟩))
  factory : (root : String) → Except PolicyJson.PublicationError (Ready ⟨model, root, schema⟩)

def Program.entries (program : Program model schema) := program.retained.get

def prepareProgram (provider : Operations) (model : PolicyModules.Model) (schema : Schema)
    (roots : List String) : Except Error (Program model schema) := do
  let selected ← (prepareWithFacts provider).mapError .missingCapability
  let facts := SchemaFacts.prepare schema
  let prepared := model.prepareC4
  let factory := fun root => selected ⟨model, root, schema⟩ prepared facts
  let entries ← Validation.traverse (fun root =>
    ((factory root).mapError (Error.context root)).map
      (fun ready => (⟨root, ready⟩ : (root : String) × Ready ⟨model, root, schema⟩))) roots.eraseDups
  return ⟨Thunk.pure entries, factory⟩

/-- A typed preparation descriptor. Construction retains only its actual inputs;
validation runs at first use and its successful Program is shared thereafter.
The supplied proof is erased; there is no unchecked runtime admission. -/
def deferProgram (provider : Operations) (model : PolicyModules.Model) (schema : Schema)
    (roots : List String) (valid : (prepareProgram provider model schema roots).toOption.isSome) :
    Program model schema :=
  let pending := Thunk.mk fun _ => (prepareProgram provider model schema roots).toOption.get valid
  ⟨Thunk.mk fun _ => pending.get.entries, fun root => pending.get.factory root⟩

theorem deferProgram_eq (provider : Operations) (model : PolicyModules.Model) (schema : Schema)
    (roots : List String) (valid : (prepareProgram provider model schema roots).toOption.isSome) :
    deferProgram provider model schema roots valid =
      (prepareProgram provider model schema roots).toOption.get valid := by
  unfold deferProgram
  generalize (prepareProgram provider model schema roots).toOption.get valid = actual
  cases actual with
  | mk retained factory =>
    cases retained with
    | mk build =>
      congr 2

private theorem traverse_length {E A B : Type} (check : A → Except E B) (items : List A)
    (result : List B) (success : Validation.traverse check items = .ok result) :
    result.length = items.length := by
  induction items generalizing result with
  | nil => simp [Validation.traverse] at success; subst result; rfl
  | cons head tail ih =>
    simp only [Validation.traverse] at success
    cases h : check head with
    | error error => simp [h, Except.bind] at success
    | ok value =>
      cases t : Validation.traverse check tail with
      | error error => simp [h, t, Except.bind, Except.map] at success
      | ok rest =>
        simp [h, t, Except.bind, Except.map] at success
        subst result
        simp [ih rest t]

/-- Retention counts actual distinct requested roots, without a process-RSS claim. -/
theorem prepareProgram_retained (provider : Operations) (model : PolicyModules.Model)
    (schema : Schema) (roots : List String) (program : Program model schema)
    (success : prepareProgram provider model schema roots = .ok program) :
    program.entries.length = roots.eraseDups.length := by
  unfold prepareProgram at success
  cases prepared : prepareWithFacts provider with
  | error error => simp [prepared, Except.mapError, bind, Except.bind] at success
  | ok selected =>
    simp only [prepared, Except.mapError, bind, Except.bind, pure, Except.pure] at success
    split at success
    · simp_all
    · rename_i entries built
      simp only [Except.ok.injEq] at success
      subst program
      exact traverse_length _ _ entries built

def Program.find? (program : Program model schema) (root : String) :
    Option (Ready ⟨model, root, schema⟩) :=
  program.entries.findSome? fun entry =>
    if same : entry.1 = root then some (same ▸ entry.2) else none

/-- Keep the original open root interface. Nonretained roots use the same
prepared operations; they never fall back to unchecked direct authorization. -/
def Program.at (program : Program model schema) (root : String) :
    Except Error (Ready ⟨model, root, schema⟩) :=
  match program.find? root with
  | some ready => .ok ready
  | none => (program.factory root).mapError (.context root)

def Program.publish (program : Program model schema) (root : String) :
    Except Error (PolicyJson.Publication model root schema) := do
  let ready ← program.at root
  ready.publish.get.mapError (.context root)

def Program.authorize (program : Program model schema) (root : String)
    (requests : List Request) (entities : Entities) :
    Except Error (Authorization.Compound.Receipt model root requests entities) := do
  let ready ← program.at root
  return ready.authorize requests entities

def Program.response (program : Program model schema) (root : String)
    (request : Request) (entities : Entities) :=
  (program.authorize root [request] entities).map (·.singleResponse)

/-- Preserve the selected single-request response in the existing layer receipt. -/
def Ready.authorizeLayer (ready : Ready ⟨model, root, schema⟩)
    (request : Request) (entities : Entities) : Authorization.Compound.LayerReceipt model entities :=
  let receipt := ready.authorize [request] entities
  { root, request, policies := receipt.policies, compiled := receipt.compiled
    response := receipt.singleResponse
    evaluated := receipt.singleResponse_evaluated }

theorem Ready.authorizeLayer_response (ready : Ready ⟨model, root, schema⟩)
    (request : Request) (entities : Entities) :
    (ready.authorizeLayer request entities).response =
      isAuthorized request entities ready.checked.policies := by
  simp [Ready.authorizeLayer, Authorization.Compound.Receipt.singleResponse, ready.aligned]

/-- Checked multi-root authorization retains input order and the first failed
root. The legacy compile-only API keeps its weaker admission boundary. -/
def Program.authorizeLayers (program : Program model schema)
    (checks : List (String × Request)) (entities : Entities) :
    Except Error (List (Authorization.Compound.LayerReceipt model entities)) :=
  Validation.traverse (fun (root, request) => do
    let ready ← program.at root
    return ready.authorizeLayer request entities) checks

theorem Program.authorizeLayers_append (program : Program model schema)
    (left right : List (String × Request)) (entities : Entities) :
    program.authorizeLayers (left ++ right) entities =
      (program.authorizeLayers left entities).bind (fun first =>
        (program.authorizeLayers right entities).map (first ++ ·)) :=
  Validation.traverse_append _ left right

/-- Render current inputs using this exact checked snapshot and selected methods. -/
def Ready.authorizationCase (ready : Ready context) (name revision : String)
    (request : Request) (entities : Entities) : Except String Lean.Json := do
  let publication ← ready.publish.get.mapError
    (fun cause => Error.message (.context context.root cause))
  let layer := ready.authorizeLayer request entities
  have same : layer.policies = publication.policies :=
    Except.ok.inj (layer.compiled.symm.trans publication.compiled)
  have request_eq : layer.request = request := rfl
  PolicyJson.authorizationCaseData name revision publication.policies publication.json
    request entities layer.response publication.serialized (by simpa only [same, request_eq] using layer.evaluated)

def Program.authorizationCase (program : Program model schema) (name revision root : String)
    (request : Request) (entities : Entities) : Except String Lean.Json := do
  let ready ← (program.at root).mapError Error.message
  ready.authorizationCase name revision request entities

/-- Keep semantic inputs and response evidence; defer request/entity JSON to output. -/
def Ready.case (ready : Ready context) (name revision : String)
    (request : Request) (entities : Entities) : Except String Transport.Case := do
  let publication ← ready.publish.get.mapError
    (fun cause => Error.message (.context context.root cause))
  have same : ready.checked.policies = publication.policies :=
    Except.ok.inj (ready.checked.compiled.symm.trans publication.compiled)
  return {
    name, revision
    policy := {
      policies := publication.policies
      snapshot := publication.snapshot
      aligned := by simpa only [publication.snapshot_value] using publication.serialized
      identifiers := publication.identifiers }
    request, entities
    response := Thunk.mk fun _ => (ready.authorizeLayer request entities).response
    evaluated := by
      change (ready.authorizeLayer request entities).response = _
      simpa only [same] using ready.authorizeLayer_response request entities }

def Program.case (program : Program model schema) (name revision root : String)
    (request : Request) (entities : Entities) : Except String Transport.Case := do
  let ready ← (program.at root).mapError Error.message
  ready.case name revision request entities

end CedarPooSpec.Functional
