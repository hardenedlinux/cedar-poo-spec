import CedarPooSpec.PolicyJson
import CedarPooSpec.CompoundAuthorization
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
  | .compile => Except PolicyJson.PublicationError (Compiled context.model context.root)
  | .validate => Compiled context.model context.root →
      Except PolicyJson.PublicationError (Validated context.model context.root context.schema)
  | .publish => Validated context.model context.root context.schema →
      Except PolicyJson.PublicationError (PolicyJson.Publication context.model context.root context.schema)
  | .authorize => Validated context.model context.root context.schema →
      (requests : List Request) → (entities : Entities) →
      CompoundAuthorization.Receipt context.model context.root requests entities

abbrev Operations := Provider Context Capability Value
abbrev required : List Capability := [.compile, .validate, .publish, .authorize]
abbrev Data (context : Context) := Requirements.Results Value context required

def cedar : Operations
  | .compile => some fun context =>
      (PolicyPreparation.compile context.model context.root).mapError .composition
  | .validate => some fun context compiled =>
      PolicyPreparation.check compiled context.schema
        PolicyJson.PublicationError.schema PolicyJson.PublicationError.policy
  | .publish => some fun _ checked => PolicyJson.publishValidated checked
  | .authorize => some fun _ checked requests entities =>
      ⟨checked.policies, checked.compiled,
        requests.map (fun request => isAuthorized request entities checked.policies), rfl⟩

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
    CompoundAuthorization.Receipt context.model context.root requests entities
  aligned : ∀ requests entities,
    (authorize requests entities).responses = requests.map (fun request =>
      isAuthorized request entities checked.policies)

theorem Ready.allowed_eq (ready : Ready context) (requests : List Request) (entities : Entities) :
    (ready.authorize requests entities).allowed =
      (!requests.isEmpty && (requests.map (fun request =>
        isAuthorized request entities ready.checked.policies)).all (fun response =>
          response.decision == .allow && response.erroringPolicies.isEmpty)) := by
  simp only [CompoundAuthorization.Receipt.allowed, ready.aligned]

def construct (context : Context) (data : Data context) (contract : Coherent context data) :
    Except PolicyJson.PublicationError (Ready context) := do
  let compiled ← data.1
  let checked ← data.2.1 compiled
  return {
    checked
    publish := Thunk.mk fun _ => data.2.2.1 checked
    authorize := data.2.2.2.1 checked
    aligned := fun requests entities => (contract checked requests entities).2 }

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
  entries : List ((root : String) × Ready ⟨model, root, schema⟩)
  factory : Factory Context (fun context => Except PolicyJson.PublicationError (Ready context))

def prepareProgram (provider : Operations) (model : PolicyModules.Model) (schema : Schema)
    (roots : List String) : Except Error (Program model schema) := do
  let factory ← (prepare provider).mapError .missingCapability
  let entries ← Validation.traverse (fun root =>
    ((factory ⟨model, root, schema⟩).mapError (Error.context root)).map
      (fun ready => (⟨root, ready⟩ : (root : String) × Ready ⟨model, root, schema⟩))) roots.eraseDups
  return ⟨entries, factory⟩

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
  | none => (program.factory ⟨model, root, schema⟩).mapError (.context root)

def Program.publish (program : Program model schema) (root : String) :
    Except Error (PolicyJson.Publication model root schema) := do
  let ready ← program.at root
  ready.publish.get.mapError (.context root)

def Program.authorize (program : Program model schema) (root : String)
    (requests : List Request) (entities : Entities) :
    Except Error (CompoundAuthorization.Receipt model root requests entities) := do
  let ready ← program.at root
  return ready.authorize requests entities

def Program.authorizationCase (program : Program model schema) (name revision root : String)
    (request : Request) (entities : Entities) : Except String Lean.Json := do
  let ready ← (program.at root).mapError Error.message
  let publication ← ready.publish.get.mapError (fun cause => Error.message (.context root cause))
  let receipt := ready.authorize [request] entities
  match h : receipt.responses with
  | [response] =>
      have same : publication.policies = ready.checked.policies :=
        Except.ok.inj (publication.compiled.symm.trans ready.checked.compiled)
      have evaluated : response = isAuthorized request entities publication.policies := by
        have aligned := ready.aligned [request] entities
        change receipt.responses = _ at aligned
        rw [h] at aligned
        rw [same]
        exact (List.cons.inj aligned).1
      PolicyJson.authorizationCaseData name revision publication.policies publication.json
        request entities response publication.serialized evaluated
  | _ => throw "Cedar single-request receipt invariant failed"

end CedarPooSpec.Functional
