import CedarPooSpec.Transport.SourceTable

/-! One bulk transport for every applicable manifest, including schema evolution.
Standalone Cedar manifests remain the independent public authoring projection. -/
namespace CedarPooSpec.Transport
private structure Pools where
  policies : SourcePool .policy := {}
  entities : SourcePool .entities := {}
  schemas : SourcePool .schema := {}
private abbrev Encode := StateT Pools (Except String)
private def object (json : Lean.Json) : Except String (List (String × Lean.Json)) :=
  return (← json.getObj?).toList
private def field (json : Lean.Json) (key : String) : Except String Lean.Json := json.getObjVal? key
private def policyRef (value : Lean.Json) : Encode (SourceRef .policy) := do
  let state ← get
  let published := state.policies.publish value
  set {state with policies := published.next}
  return published.reference
private def entitiesRef (value : Lean.Json) : Encode (SourceRef .entities) := do
  let state ← get
  let published := state.entities.publish value
  set {state with entities := published.next}
  return published.reference
private def schemaRef (value : Lean.Json) : Encode (SourceRef .schema) := do
  let state ← get
  let published := state.schemas.publish value
  set {state with schemas := published.next}
  return published.reference
private def manifest (value : Lean.Json) : Encode Lean.Json := do
  let cases ← (← field value "cases").getArr?
  let mut rows := #[]
  let mut bindings : Std.HashMap String Nat := {}
  for row in cases do
    let policy ← policyRef (← field row "policies")
    let entities ← entitiesRef (← field row "entities")
    let revision ← (← field row "revision").getStr?
    if let some prior := bindings[revision]? then
      unless prior = policy.index do throw s!"conflicting source for revision: {revision}"
    bindings := bindings.insert revision policy.index
    let fields := (← object row).filter fun field =>
      field.1 != "policies" && field.1 != "entities"
    rows := rows.push (Lean.Json.mkObj (fields ++ [
      ("policy_ref", Lean.toJson policy.index), ("entities_ref", Lean.toJson entities.index)]))
  let fields := (← object value).filter fun field => field.1 != "cases" && field.1 != "schema"
  let mut fields := fields ++ [("cases", .arr rows),
    ("revision_sources", Lean.Json.mkObj (bindings.toList.map fun (key, index) => (key, Lean.toJson index)))]
  if let .ok schema := field value "schema" then
    let ref ← schemaRef schema
    fields := fields ++ [("schema_ref", Lean.toJson ref.index), ("manifest_kind", Lean.toJson "schema-bound")]
  else
    fields := fields ++ [("manifest_kind", Lean.toJson "raw")]
  return Lean.Json.mkObj fields
private def payload (value : Lean.Json) : Encode Lean.Json := do
  if (field value "cases").isOk then return ← manifest value
  if (field value "before").isOk && (field value "after").isOk then
    return Lean.Json.mkObj [("before", ← manifest (← field value "before")),
      ("after", ← manifest (← field value "after"))]
  if let .ok rows := value.getArr? then
    if !rows.isEmpty && rows.all (fun row => (field row "root").isOk && (field row "policies").isOk) then
      let rows ← rows.mapM fun row => do
        let ref ← policyRef (← field row "policies")
        return Lean.Json.mkObj [("root", ← field row "root"), ("policy_ref", Lean.toJson ref.index)]
      return .arr rows
  return value

/-- References are transport locations only. SDK admission and both authorizers
remain the consumer's per-revision/per-request obligations. -/
def sourceCatalogFrom (entries : List (String × (Unit → Except String Lean.Json))) :
    Except String Lean.Json := do
  let encode : Encode (List (String × Lean.Json)) := entries.mapM fun (name, produce) => do
    let value ← produce ()
    return (name, ← payload value)
  let (entries, pools) ← encode.run {}
  return Lean.Json.mkObj [
    ("format_version", Lean.toJson (2 : Nat)),
    ("sources", Lean.Json.mkObj [
      ("policies", .arr (pools.policies.entries.map (·.value))),
      ("entities", .arr (pools.entities.entries.map (·.value))),
      ("schemas", .arr (pools.schemas.entries.map (·.value)))]),
    ("entries", Lean.Json.mkObj entries)]
/-- Pure snapshots use the same publisher and ordering as factory publication. -/
def sourceCatalog (entries : List (String × Lean.Json)) : Except String Lean.Json :=
  sourceCatalogFrom (entries.map fun (name, value) => (name, fun _ => .ok value))

end CedarPooSpec.Transport
