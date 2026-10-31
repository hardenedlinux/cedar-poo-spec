import CedarPooSpec.Pseudonymization.TableBatchWire
import Lean.Data.Json

namespace CedarPooSpec.Pseudonymization.TableBatchFixture

open CedarPooSpec.Pseudonymization Lean

def profile : TokenProfile :=
  { mode := .aesSiv, scope := "study", lineage :=
    { tenant := "tenant-a", keyDomain := "study-key",
      tokenKeyVersion := "dek-1", transformVersion := "recipe-1",
      wrappingVersion := "kek-1" } }

def recipe : AesSivTableRecipe :=
  { dataset := "research", valueField := "patient_id",
    contextField := "study_context", profile,
    admittedContext := some "study-a" }

def row (value context : String) : TableRow :=
  { fields := [("patient_id", value), ("study_context", context)] }

def baseRows : List AesSivTableBatchRow :=
  [⟨0, row "patient-1" "study-a"⟩, ⟨1, row "patient-2" "study-a"⟩]

def cases : List (String × AesSivTableRecipe × List AesSivTableBatchRow × Nat × Nat) :=
  [("two-rows", recipe, baseRows, 2, 100),
   ("two-contexts", { recipe with admittedContext := none },
     [⟨0, row "patient-1" "study-a"⟩, ⟨1, row "patient-2" "study-b"⟩], 2, 100),
   ("empty", recipe, [], 2, 100),
   ("zero-row-budget", recipe, baseRows, 0, 100),
   ("unbounded-row-budget", recipe, baseRows, 257, 100),
   ("too-many-rows", recipe, baseRows, 1, 100),
   ("duplicate-ordinal", recipe, [⟨0, row "patient-1" "study-a"⟩,
     ⟨0, row "patient-2" "study-a"⟩], 2, 100),
   ("descending-ordinal", recipe, [⟨1, row "patient-1" "study-a"⟩,
     ⟨0, row "patient-2" "study-a"⟩], 2, 100),
   ("missing-value", recipe, [⟨0, { fields := [("study_context", "study-a")] }⟩], 2, 100),
   ("duplicate-context", recipe, [⟨0, { fields := [("patient_id", "patient-1"),
     ("study_context", "study-a"), ("study_context", "study-a")] }⟩], 2, 100),
   ("changed-context", recipe, [⟨0, row "patient-1" "study-b"⟩], 2, 100),
   ("selected-byte-budget", recipe, baseRows, 2, 10),
   ("wrong-mode", { recipe with profile := { profile with mode := .hmacSha256 } },
     baseRows, 2, 100)]

def wireSelected : List AesSivTableBatchInput :=
  [⟨0, ⟨"patient-1", "study-a"⟩⟩, ⟨1, ⟨"patient-2", "study-a"⟩⟩]

def wireRows : List TableBatchWireRow :=
  [⟨"c3ludGhldGljLWNpcGhlcnRleHQtMQ==", "study-a", "r0"⟩,
   ⟨"c3ludGhldGljLWNpcGhlcnRleHQtMg==", "study-a", "r1"⟩]

def wireResponse : TableBatchWireResponse :=
  ⟨wireRows, 2, 0⟩

def wireCases : List (String × List AesSivTableBatchInput × TableBatchWireResponse) :=
  [("two-rows", wireSelected, wireResponse),
   ("two-contexts",
     [⟨0, ⟨"patient-1", "study-a"⟩⟩, ⟨1, ⟨"patient-2", "study-b"⟩⟩],
     { wireResponse with rows := [wireRows[0]!, ⟨wireRows[1]!.value, "study-b", "r1"⟩] }),
   ("swapped-same-context", wireSelected,
     { wireResponse with rows := [wireRows[1]!, wireRows[0]!] }),
   ("duplicate-marker", wireSelected,
     { wireResponse with rows := [wireRows[0]!, { wireRows[1]! with marker := "r0" }] }),
   ("missing-row", wireSelected,
     { wireResponse with rows := [wireRows[0]!] }),
   ("extra-row", wireSelected,
     { wireResponse with rows := wireRows ++ [wireRows[0]!] }),
   ("changed-context", wireSelected,
     { wireResponse with rows := [⟨wireRows[0]!.value, "study-b", "r0"⟩, wireRows[1]!] }),
   ("unchanged-value", wireSelected,
     { wireResponse with rows := [⟨"patient-1", "study-a", "r0"⟩, wireRows[1]!] }),
   ("empty-token", wireSelected,
     { wireResponse with rows := [⟨"", "study-a", "r0"⟩, wireRows[1]!] }),
   ("partial-success", wireSelected,
     { wireResponse with successCount := 1 }),
   ("reported-error", wireSelected,
     { wireResponse with errorCount := 1 }),
   ("empty-selection", [], wireResponse)]

def errorName : TableBatchError → String
  | .empty => "empty"
  | .invalidBudget => "invalid-budget"
  | .tooManyRows => "too-many-rows"
  | .ordinalOrder => "ordinal-order"
  | .selection .invalidRecipe => "invalid-recipe"
  | .selection .missingOrDuplicateValue => "value-field"
  | .selection .missingOrDuplicateContext => "context-field"
  | .selection .contextNotAdmitted => "context-not-admitted"
  | .tooManyBytes => "too-many-bytes"

private def rowJson (entry : AesSivTableBatchRow) : Json :=
  Json.mkObj [("ordinal", toJson entry.ordinal),
    ("fields", toJson (entry.row.fields.map fun (name, value) =>
      Json.mkObj [("name", toJson name), ("value", toJson value)]))]

private def caseJson
    (entry : String × AesSivTableRecipe × List AesSivTableBatchRow × Nat × Nat) : Json :=
  let (name, recipe, rows, maxRows, maxBytes) := entry
  let result := recipe.selectBatch rows maxRows maxBytes
  Json.mkObj [("name", toJson name), ("mode", toJson (if recipe.profile.mode == .aesSiv then
      "aes-siv" else "hmac-sha256")),
    ("admitted_context", toJson recipe.admittedContext),
    ("rows", toJson (rows.map rowJson)),
    ("max_rows", toJson maxRows), ("max_utf8_bytes", toJson maxBytes),
    ("result", match result with
      | .ok selected => Json.mkObj [("allow", toJson true),
          ("ordinals", toJson (selected.map (·.ordinal))),
          ("values", toJson (selected.map (·.input.value))),
          ("contexts", toJson (selected.map (·.input.context)))]
      | .error reason => Json.mkObj [("allow", toJson false),
          ("error", toJson (errorName reason))])]

private def wireCaseJson
    (entry : String × List AesSivTableBatchInput × TableBatchWireResponse) : Json :=
  let (name, selected, response) := entry
  Json.mkObj [("name", toJson name),
    ("selected", toJson (selected.map fun row => Json.mkObj
      [("ordinal", toJson row.ordinal), ("value", toJson row.input.value),
       ("context", toJson row.input.context)])),
    ("response_rows", toJson (response.rows.map fun row => Json.mkObj
      [("value", toJson row.value), ("context", toJson row.context),
       ("marker", toJson row.marker)])),
    ("success_count", toJson response.successCount),
    ("error_count", toJson response.errorCount),
    ("allow", toJson (response.admitted selected))]

def fixture : Json :=
  Json.mkObj [("schema", toJson "google-table-batch-v1"),
    ("cases", toJson (cases.map caseJson)),
    ("wire_cases", toJson (wireCases.map wireCaseJson))]

end CedarPooSpec.Pseudonymization.TableBatchFixture
