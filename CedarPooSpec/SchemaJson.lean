import CedarPooSpec.SchemaAdmission
import CedarPooSpec.Transport.Case
import Lean

/-! A bounded projection of Cedar Lean schemas into Cedar's public JSON schema. -/

namespace CedarPooSpec.SchemaJson

open Cedar.Spec Cedar.Validation Cedar.Data

inductive Error where
  | invalidSchema (message : String)
  | unsupportedBooleanRefinement
  | unsupportedActionType (action : EntityUID)
  | typeDepthExceeded
  deriving Repr

private def obj (fields : List (String × Lean.Json)) : Lean.Json :=
  Lean.Json.mkObj fields

mutual
private def typeFields : Nat → CedarType → Except Error (List (String × Lean.Json))
  | 0, _ => .error .typeDepthExceeded
  | _fuel + 1, .bool .anyBool => .ok [("type", Lean.toJson "Boolean")]
  | _fuel + 1, .bool _ => .error .unsupportedBooleanRefinement
  | _fuel + 1, .int => .ok [("type", Lean.toJson "Long")]
  | _fuel + 1, .string => .ok [("type", Lean.toJson "String")]
  | _fuel + 1, .entity ty => .ok [("type", Lean.toJson "Entity"), ("name", Lean.toJson (toString ty))]
  | fuel + 1, .set element => do
      return [("type", Lean.toJson "Set"), ("element", obj (← typeFields fuel element))]
  | fuel + 1, .record fields => do
      return [("type", Lean.toJson "Record"), ("attributes", ← attributeFields fuel fields)]
  | _fuel + 1, .ext .ipAddr => .ok [("type", Lean.toJson "Extension"), ("name", Lean.toJson "ipaddr")]
  | _fuel + 1, .ext .decimal => .ok [("type", Lean.toJson "Extension"), ("name", Lean.toJson "decimal")]
  | _fuel + 1, .ext .datetime => .ok [("type", Lean.toJson "Extension"), ("name", Lean.toJson "datetime")]
  | _fuel + 1, .ext .duration => .ok [("type", Lean.toJson "Extension"), ("name", Lean.toJson "duration")]

private def attributeFields (fuel : Nat) (fields : RecordType) : Except Error Lean.Json := do
  let entries ← fields.toList.mapM fun (name, qualified) => do
    let ty ← typeFields fuel qualified.getType
    let optional := if qualified.isRequired then [] else [("required", Lean.toJson false)]
    return (name, obj (ty ++ optional))
  return obj entries
end

private def recordType (fields : RecordType) : Except Error Lean.Json := do
  return obj [("type", Lean.toJson "Record"), ("attributes", ← attributeFields 128 fields)]

private def entityEntry : EntitySchemaEntry → Except Error Lean.Json
  | .enum ids => .ok (obj [("enum", Lean.toJson ids.toList)])
  | .standard entry => do
      let mut fields := [("memberOfTypes", Lean.toJson (entry.ancestors.toList.map toString)),
        ("shape", ← recordType entry.attrs)]
      if let some tags := entry.tags then
        fields := fields ++ [("tags", obj (← typeFields 128 tags))]
      return obj fields

private def actionEntry (uid : EntityUID) (entry : ActionSchemaEntry) : Except Error Lean.Json := do
  if uid.ty.id != "Action" then
    throw (.unsupportedActionType uid)
  let members := entry.ancestors.toList.map fun parent =>
    obj [("id", Lean.toJson parent.eid), ("type", Lean.toJson (toString parent.ty))]
  return obj [
    ("memberOf", Lean.toJson members),
    ("appliesTo", obj [
      ("principalTypes", Lean.toJson (entry.appliesToPrincipal.toList.map toString)),
      ("resourceTypes", Lean.toJson (entry.appliesToResource.toList.map toString)),
      ("context", ← recordType entry.context)])]

def schema (input : Schema) : Except Error Lean.Json := do
  if let .error error := SchemaAdmission.validateDefinitions input then
    throw (.invalidSchema (toString error))
  if let .error error := input.validateWellFormed then
    throw (.invalidSchema (toString error))
  let paths := ((input.ets.toList.map fun (pair : EntityType × EntitySchemaEntry) => pair.1.path) ++
    (input.acts.toList.map fun (pair : EntityUID × ActionSchemaEntry) => pair.1.ty.path)).eraseDups
  let entries ← paths.mapM fun path => do
    let entityTypes ← (input.ets.toList.filter fun (pair : EntityType × EntitySchemaEntry) => pair.1.path == path).mapM
      fun (pair : EntityType × EntitySchemaEntry) => do return (pair.1.id, ← entityEntry pair.2)
    let actions ← (input.acts.toList.filter fun (pair : EntityUID × ActionSchemaEntry) => pair.1.ty.path == path).mapM
      fun (pair : EntityUID × ActionSchemaEntry) => do return (pair.1.eid, ← actionEntry pair.1 pair.2)
    return (String.intercalate "::" path,
      obj [("entityTypes", obj entityTypes), ("actions", obj actions)])
  return obj entries

def validatedManifest (input : Schema) (cases : List Lean.Json) : Except String Lean.Json := do
  let projected ← (schema input).mapError reprStr
  return obj [("schema", projected), ("cases", Lean.toJson cases)]

/-- Typed production inventory; standalone JSON is derived only at the boundary. -/
def manifest (input : Schema) (cases : List Transport.Case) : Except String Transport.Manifest := do
  let projected ← (schema input).mapError reprStr
  return ⟨cases, some (Transport.SourceSnapshot.ofJson projected)⟩

end CedarPooSpec.SchemaJson
