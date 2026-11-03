import CedarPooSpec.Transport.Case

namespace CedarPooSpec.SchemaJson
open Cedar.Validation

def validatedManifest (input : Schema) (cases : List Lean.Json) : Except String Lean.Json := do
  let projected ← (schema input).mapError reprStr
  return Lean.Json.mkObj [("schema", projected), ("cases", Lean.toJson cases)]

/-- Typed production inventory; standalone JSON is derived only at the boundary. -/
def manifest (input : Schema) (cases : List Transport.Case) : Except String Transport.Manifest := do
  let projected ← Transport.SchemaSource.capture input
  return ⟨cases, some projected⟩

end CedarPooSpec.SchemaJson
