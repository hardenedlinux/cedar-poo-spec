import CedarPooSpec.PolicyJson
import LeanPoo.Functional.ContextSlot

/-! Typed semantic cases. JSON is a boundary projection, not retained case state. -/
namespace CedarPooSpec.Transport
open Cedar.Spec

structure PolicySource where
  policies : Policies
  snapshot : SourceSnapshot .policy
  aligned : PolicyJson.policySet policies = .ok snapshot.value
  identifiers : Thunk { value : Lean.Json // value = Lean.toJson (policies.map Policy.id) } :=
    Thunk.mk fun _ => ⟨Lean.toJson (policies.map Policy.id), rfl⟩

theorem PolicySource.identifiers_bound (source : PolicySource) :
    source.identifiers.get.val = Lean.toJson (source.policies.map Policy.id) :=
  source.identifiers.get.property

/-- Request, entities and response evidence belong to this exact semantic case. -/
structure Case where
  name : String
  revision : String
  policy : PolicySource
  request : Request
  entities : Entities
  response : Thunk Response
  evaluated : response.get = isAuthorized request entities policy.policies

/-- A manifest is a typed inventory; schema projection still admits no SDK policy. -/
structure Manifest where
  cases : List Case
  schema : Option (SourceSnapshot .schema) := none

structure PolicyArtifact where
  root : String
  source : SourceSnapshot .policy

inductive Entry where
  | manifest (value : Manifest)
  | evolution (before after : Manifest)
  | artifacts (values : List PolicyArtifact)
  | data (value : Lean.Json)

/-- A typed native input and its interpreter. Keeping input separate from code
prevents closed manifest computations from becoming persistent global values. -/
structure EntryProducer where
  Input : Type
  input : Input
  produce : Input → Except String Entry

def EntryProducer.of {α : Type} (input : α) (produce : α → Except String Entry) : EntryProducer :=
  ⟨α, input, produce⟩

def EntryProducer.run (producer : EntryProducer) : Except String Entry :=
  producer.produce producer.input

theorem EntryProducer.run_of {α : Type} (input : α) (produce : α → Except String Entry) :
    (EntryProducer.of input produce).run = produce input := rfl

private def entitySource (store : Entities) : Except String (SourceSnapshot .entities) := do
  return SourceSnapshot.ofJson (← (PolicyJson.entities store).mapError reprStr)

open LeanPoo.Functional
-- Select the public ordered representation's lawful short-circuit comparison.
-- These instances stay local to this adapter; Cedar's admission is unchanged.
local instance {α β : Type} [BEq α] [BEq β] : BEq (Cedar.Data.Map α β) where
  beq left right := left.toList == right.toList
local instance {α β : Type} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] :
    LawfulBEq (Cedar.Data.Map α β) where
  rfl := by
    intro value
    change (value.toList == value.toList) = true
    exact BEq.rfl
  eq_of_beq := by
    intro left right equal
    cases left with
    | mk left =>
      cases right with
      | mk right =>
        have same : left = right := eq_of_beq equal
        cases same
        rfl
private abbrev EntityValue (_ : Entities) (_ : Unit) :=
  Except String (SourceSnapshot .entities)
private def entityFamily :
    @Requirements.Certified Entities Unit EntityValue [()]
      (fun store data => data.1 = entitySource store) where
  factories := (entitySource, PUnit.unit)
  valid := fun _ => rfl
abbrev EntitySlot := Requirements.ContextSlot entityFamily

def EntitySlot.empty : EntitySlot := Requirements.ContextSlot.empty entityFamily

def EntitySlot.read (slot : EntitySlot) (store : Entities) :
    Except String (SourceSnapshot .entities) × EntitySlot × Bool :=
  slot.consume (fun _ data _ => data.1) store

theorem EntitySlot.read_value (slot : EntitySlot) (store : Entities) :
    (slot.read store).1 = entitySource store := by
  rw [EntitySlot.read, Requirements.ContextSlot.consume_value]
  rfl

theorem EntitySlot.bound (slot : EntitySlot) : slot.retained.toList.length ≤ 1 := by
  cases slot.retained <;> simp

/-- Common fields are generated once per case; source values stay separate. -/
def Case.fields (input : Case) : Except String (List (String × Lean.Json)) := do
  let request ← (PolicyJson.request input.request).mapError reprStr
  let response := input.response.get
  return [
    ("name", Lean.toJson input.name), ("revision", Lean.toJson input.revision),
    ("policy_ids", input.policy.identifiers.get.val),
    ("request", request),
    ("expected", Lean.toJson (match response.decision with | .allow => "allow" | .deny => "deny")),
    ("expected_reasons", Lean.toJson response.determiningPolicies.toList),
    ("expected_error_policies", Lean.toJson response.erroringPolicies.toList)]

def Case.toJson (input : Case) : Except String Lean.Json := do
  let source := input.policy.snapshot
  let entities ← entitySource input.entities
  let request ← (PolicyJson.request input.request).mapError reprStr
  let response := input.response.get
  return Lean.Json.mkObj [
    ("name", Lean.toJson input.name), ("revision", Lean.toJson input.revision),
    ("policy_ids", Lean.toJson (input.policy.policies.map Policy.id)),
    ("policies", source.value), ("entities", entities.value), ("request", request),
    ("expected", Lean.toJson (match response.decision with | .allow => "allow" | .deny => "deny")),
    ("expected_reasons", Lean.toJson response.determiningPolicies.toList),
    ("expected_error_policies", Lean.toJson response.erroringPolicies.toList)]

def Manifest.toJson (input : Manifest) : Except String Lean.Json := do
  let cases ← input.cases.mapM Case.toJson
  return Lean.Json.mkObj ((match input.schema with
    | none => [] | some schema => [("schema", schema.value)]) ++ [("cases", Lean.toJson cases)])

def Entry.toJson : Entry → Except String Lean.Json
  | .manifest value => value.toJson
  | .evolution before after => do
      return Lean.Json.mkObj [("before", ← before.toJson), ("after", ← after.toJson)]
  | .artifacts values => .ok (Lean.toJson (values.map fun value =>
      Lean.Json.mkObj [("root", Lean.toJson value.root), ("policies", value.source.value)]))
  | .data value => .ok value

/-- Project this actual case through the existing independent inline serializer. -/
theorem Case.inline_projection (input : Case) :
    input.toJson = PolicyJson.authorizationCaseData input.name input.revision
      input.policy.policies input.policy.snapshot.value input.request input.entities input.response.get
      input.policy.aligned input.evaluated := by
  simp only [Case.toJson, entitySource, PolicyJson.authorizationCaseData]
  cases PolicyJson.entities input.entities <;>
    cases PolicyJson.request input.request <;> rfl

end CedarPooSpec.Transport
