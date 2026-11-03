import Examples.ManifestCatalog
import Productions.Gateway.ReviewedEffects

namespace CedarPooSpec.ReviewedEffectCatalog
open Transport Production.ReviewedEffects
private def qualified (manifest : Manifest) (row : Case) : Except String Plan := do
  let some origin := row.policy.origin | throw "missing proof-bound C4 origin"
  let schema ← match manifest.schema, origin.schema with
    | some schema, _ => pure schema
    | none, some native => SchemaSource.capture native
    | none, none => throw "compile-only Case has no schema"
  if !(Cedar.Validation.validate row.policy.policies schema.meaning).isOk then
    throw "strict policy/schema validation refused"
  if !(Cedar.Validation.validateRequest schema.meaning row.request).isOk then
    throw "strict request validation refused"
  if !(Cedar.Validation.validateEntities schema.meaning row.entities).isOk then
    throw "strict entity validation refused"
  plan row.policy schema
private def groups (manifest : Manifest) : Except String (List (Plan × List Case) × List Lean.Json) := do
  let mut result : List (Plan × List Case) := []
  let mut keys : List String := []
  let mut refused := []
  for row in manifest.cases do
    match qualified manifest row with
    | .error cause => refused := refused ++ [Lean.Json.mkObj [
        ("name", Lean.toJson row.name), ("revision", Lean.toJson row.revision), ("reason", Lean.toJson cause)]]
    | .ok prepared =>
      let key := Lean.Json.arr #[← modelJson prepared, prepared.schema.value, Lean.toJson prepared.beforeRoot] |>.compress
      if let some index := keys.idxOf? key then
        result := result.modify index (fun (plan, rows) => (plan, rows ++ [row]))
      else
        keys := keys ++ [key]
        result := result ++ [(prepared, [row])]
  return (result, refused)

def exportEntry (name : String) (entry : Entry) : IO Lean.Json := do
  let manifests := match entry with
    | .manifest value => [(name, value)]
    | .evolution before after => [(name ++ "/before", before), (name ++ "/after", after)]
    | _ => []
  let mut outputs : Array Lean.Json := #[]
  let mut refused : Array Lean.Json := #[]
  for (label,manifest) in manifests do
    let (grouped, rejected) ← IO.ofExcept (groups manifest)
    refused := refused.push (Lean.Json.mkObj [("entry", Lean.toJson label), ("cases", Lean.toJson rejected)])
    for (plan,rows) in grouped do
      outputs := outputs.push (Lean.Json.mkObj [("entry", Lean.toJson label),
        ("plan", ← Production.ReviewedEffects.project plan rows)])
  return Lean.Json.mkObj [("format_version", Lean.toJson (1 : Nat)), ("entry", Lean.toJson name),
    ("groups", Lean.toJson outputs), ("refusals", Lean.toJson refused),
    ("original", ← IO.ofExcept (Transport.sourceCatalog [(name,entry)]))]
end CedarPooSpec.ReviewedEffectCatalog

def main (args : List String) : IO Unit := do
  let [name] := args | throw (IO.userError "expected canonical catalogue entry name")
  let some producer := CedarPooSpec.Manifests.entries.lookup name
    | throw (IO.userError "unknown catalogue entry")
  let entry ← IO.ofExcept producer.run
  let json ← CedarPooSpec.ReviewedEffectCatalog.exportEntry name entry
  IO.println json.compress
