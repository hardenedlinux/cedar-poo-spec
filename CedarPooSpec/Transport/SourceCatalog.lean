import CedarPooSpec.Transport.Case
import CedarPooSpec.Transport.Wire

/-! Both public authoring JSON and the canonical bulk wire project typed entries.
No inline case JSON is constructed and then decoded by the bulk publisher. -/
namespace CedarPooSpec.Transport
private structure Pools where
  policies : SourcePool .policy := {}
  entities : SourcePool .entities := {}
  schemas : SourcePool .schema := {}
  entitySlot : EntitySlot := EntitySlot.empty
private abbrev Encode := StateT Pools (Except String)
private def policyRef (value : SourceSnapshot .policy) : Encode (SourceRef .policy) := do
  let state ← get
  let published := state.policies.publishSnapshot value
  set {state with policies := published.next}
  return published.reference
private def entitiesRef (value : SourceSnapshot .entities) : Encode (SourceRef .entities) := do
  let state ← get
  let published := state.entities.publishSnapshot value
  set {state with entities := published.next}
  return published.reference
private def schemaRef (value : SourceSnapshot .schema) : Encode (SourceRef .schema) := do
  let state ← get
  let published := state.schemas.publishSnapshot value
  set {state with schemas := published.next}
  return published.reference
private def manifest (value : Manifest) : Encode Lean.Json := do
  let mut rows := #[]
  let mut bindings : Std.HashMap String Nat := {}
  for row in value.cases do
    let policy ← policyRef row.policy.snapshot
    let state ← get
    let (result, next, _) := state.entitySlot.read row.entities
    set {state with entitySlot := next}
    let entities ← entitiesRef (← result)
    let revision := row.revision
    if let some prior := bindings[revision]? then
      unless prior = policy.index do throw s!"conflicting source for revision: {revision}"
    bindings := bindings.insert revision policy.index
    rows := rows.push (Lean.Json.mkObj ((← row.fields) ++ [
      ("policy_ref", Lean.toJson policy.index), ("entities_ref", Lean.toJson entities.index)]))
  let mut fields := [("cases", .arr rows),
    ("revision_sources", Lean.Json.mkObj (bindings.toList.map fun (key, index) => (key, Lean.toJson index)))]
  if let some schema := value.schema then
    let ref ← schemaRef schema
    fields := fields ++ [("schema_ref", Lean.toJson ref.index), ("manifest_kind", Lean.toJson "schema-bound")]
  else
    fields := fields ++ [("manifest_kind", Lean.toJson "raw")]
  return Lean.Json.mkObj fields
private def payload : Entry → Encode Lean.Json
  | .manifest value => manifest value
  | .evolution before after => do
      return Lean.Json.mkObj [("before", ← manifest before), ("after", ← manifest after)]
  | .artifacts values => do
      let rows ← values.mapM fun row => do
        let ref ← policyRef row.source
        return Lean.Json.mkObj [("root", Lean.toJson row.root), ("policy_ref", Lean.toJson ref.index)]
      return Lean.toJson rows
  | .data value => pure value

/-- References locate complete sources only; SDK admission remains fresh. -/
def prepareCatalogFrom (entries : List (String × (Unit → Except String Entry))) :
    Except String EncodedJson := do
  let encode : Encode (List (String × Lean.Json)) := entries.mapM fun (name, produce) => do
    return (name, ← payload (← produce ()))
  let (entries, pools) ← encode.run {}
  let sources := EncodedJson.object [
    ("entities", EncodedJson.array (pools.entities.entries.toList.map EncodedJson.snapshot)),
    ("policies", EncodedJson.array (pools.policies.entries.toList.map EncodedJson.snapshot)),
    ("schemas", EncodedJson.array (pools.schemas.entries.toList.map EncodedJson.snapshot))] (by simp)
  return EncodedJson.object [
    ("entries", EncodedJson.native (Lean.Json.mkObj entries)),
    ("format_version", EncodedJson.native (Lean.toJson (2 : Nat))),
    ("sources", sources)] (by simp)

/-- Public JSON projection of the same certified envelope. -/
def sourceCatalogFrom (entries : List (String × (Unit → Except String Entry))) :
    Except String Lean.Json :=
  (prepareCatalogFrom entries).map (·.value)

def sourceCatalog (entries : List (String × Entry)) : Except String Lean.Json :=
  sourceCatalogFrom (entries.map fun (name, value) => (name, fun _ => .ok value))
end CedarPooSpec.Transport
