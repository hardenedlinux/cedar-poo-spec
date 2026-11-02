import CedarPooSpec.Transport.Case
import CedarPooSpec.Transport.Wire

/-! Both public authoring JSON and the canonical bulk wire project typed entries.
No inline case JSON is constructed and then decoded by the bulk publisher. -/
namespace CedarPooSpec.Transport
structure SourcePools where
  policies : SourcePool .policy := {}
  entities : SourcePool .entities := {}
  schemas : SourcePool .schema := {}
  entitySlot : EntitySlot := EntitySlot.empty
private abbrev Encode := StateT SourcePools (Except String)
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
private def prepareManifest (value : Manifest) : Encode EncodedJson := do
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
    rows := rows.push (EncodedJson.nativeObject ((← row.fields) ++ [
      ("policy_ref", Lean.toJson policy.index), ("entities_ref", Lean.toJson entities.index)]))
  let mut fields := [("cases", EncodedJson.array rows.toList),
    ("revision_sources", EncodedJson.nativeObject (bindings.toList.map fun (key, index) => (key, Lean.toJson index)))]
  if let some schema := value.schema then
    let ref ← schemaRef schema
    fields := fields ++ [("schema_ref", EncodedJson.native (Lean.toJson ref.index)), ("manifest_kind", EncodedJson.native (Lean.toJson "schema-bound"))]
  else
    fields := fields ++ [("manifest_kind", EncodedJson.native (Lean.toJson "raw"))]
  return EncodedJson.canonicalObject fields
def Entry.prepare : Entry → Encode EncodedJson
  | .manifest value => prepareManifest value
  | .evolution before after => do
      return EncodedJson.canonicalObject [("before", ← prepareManifest before), ("after", ← prepareManifest after)]
  | .artifacts values => do
      let rows ← values.mapM fun row => do
        let ref ← policyRef row.source
        return EncodedJson.nativeObject [("root", Lean.toJson row.root),
          ("policy_ref", Lean.toJson ref.index)]
      return EncodedJson.array rows
  | .data value => pure (EncodedJson.native value)

/-- Finish the same source pools and ordered entries; shared by the producer and
native attribution. No SDK admission or extra catalog representation is added. -/
def SourcePools.finish (pools : SourcePools) (entries : List (String × EncodedJson)) : EncodedJson :=
  let sources := EncodedJson.object [
    ("entities", EncodedJson.array (pools.entities.entries.toList.map EncodedJson.snapshot)),
    ("policies", EncodedJson.array (pools.policies.entries.toList.map EncodedJson.snapshot)),
    ("schemas", EncodedJson.array (pools.schemas.entries.toList.map EncodedJson.snapshot))] (by simp)
  EncodedJson.object [
    ("entries", EncodedJson.canonicalObject entries),
    ("format_version", EncodedJson.native (Lean.toJson (2 : Nat))),
    ("sources", sources)] (by simp)

/-- References locate complete sources only; SDK admission remains fresh. -/
def prepareCatalogFrom (entries : List (String × EntryProducer)) :
    Except String EncodedJson := do
  let encode : Encode (List (String × EncodedJson)) := entries.mapM fun (name, produce) => do
    return (name, (← Entry.prepare (← produce.run)).compact)
  let (entries, pools) ← encode.run {}
  return pools.finish entries

/-- Public JSON projection of the same certified envelope. -/
def sourceCatalogFrom (entries : List (String × EntryProducer)) :
    Except String Lean.Json :=
  (prepareCatalogFrom entries).map (·.value)

def sourceCatalog (entries : List (String × Entry)) : Except String Lean.Json :=
  sourceCatalogFrom (entries.map fun (name, value) => (name, EntryProducer.of value Except.ok))
end CedarPooSpec.Transport
