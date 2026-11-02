import CedarPooSpec.Transport.SourceTable

/-! Compositional JSON framing over complete, certified native fragments.
The certificate binds every embedded fragment to its actual JSON value. -/
namespace CedarPooSpec.Transport

private def canonicalChunks (keys : List String) (wires : List (List String)) : List String :=
  let fields := (Std.TreeMap.ofList (keys.zip wires)).toList
  ["{"] ++ ((fields.map fun (key, wire) =>
    [(Lean.Json.str key).compress, ":"] ++ wire).intersperse [","]).flatten ++ ["}"]

mutual
inductive JsonEncoding : Lean.Json → List String → Prop where
  | native (value : Lean.Json) : JsonEncoding value [value.compress]
  | array (values : List Lean.Json) (wires : List (List String))
      (items : JsonFragments values wires) :
      JsonEncoding (.arr values.toArray) (["["] ++ (wires.intersperse [","]).flatten ++ ["]"])
  | object (keys : List String) (values : List Lean.Json) (wires : List (List String))
      (lengths : keys.length = values.length) (unique : keys.Nodup)
      (items : JsonFragments values wires) :
      JsonEncoding (Lean.Json.mkObj (keys.zip values))
        (["{"] ++ (((keys.zip wires).map fun (key, wire) =>
          [(Lean.Json.str key).compress, ":"] ++ wire).intersperse [","]).flatten ++ ["}"])
  | canonicalObject (keys : List String) (values : List Lean.Json) (wires : List (List String))
      (lengths : keys.length = values.length) (items : JsonFragments values wires) :
      JsonEncoding (Lean.Json.mkObj (keys.zip values)) (canonicalChunks keys wires)
  | compact (encoding : JsonEncoding value chunks) :
      JsonEncoding value [String.join chunks]

inductive JsonFragments : List Lean.Json → List (List String) → Prop where
  | nil : JsonFragments [] []
  | cons (head : JsonEncoding value wire) (tail : JsonFragments values wires) :
      JsonFragments (value :: values) (wire :: wires)
end

theorem JsonFragments.length_eq (fragments : JsonFragments values wires) :
    values.length = wires.length := by
  induction values generalizing wires with
  | nil => cases fragments; rfl
  | cons value values ih =>
    cases fragments with
    | cons _ tail => simpa using congrArg Nat.succ (ih tail)

/-- A value and a lazy encoding with a complete compositional JSON certificate. -/
structure EncodedJson where
  semantic : Thunk Lean.Json
  rendering : Thunk (List String)
  valid : JsonEncoding semantic.get rendering.get

def EncodedJson.value (encoded : EncodedJson) : Lean.Json := encoded.semantic.get

def EncodedJson.chunks (encoded : EncodedJson) : List String := encoded.rendering.get
def EncodedJson.wire (encoded : EncodedJson) : String := String.join encoded.chunks
theorem EncodedJson.certified (encoded : EncodedJson) :
    JsonEncoding encoded.value encoded.chunks := encoded.valid
theorem EncodedJson.wire_eq (encoded : EncodedJson) :
    encoded.wire = String.join encoded.chunks := rfl

/-- Transfer only the certified rendering to an output consumer. Its closure
captures the rendering field, not the enclosing semantic JSON container. -/
def EncodedJson.detach (encoded : EncodedJson) : Thunk (List String) := encoded.rendering

theorem EncodedJson.detach_eq (encoded : EncodedJson) :
    encoded.detach.get = encoded.chunks := rfl

theorem EncodedJson.detach_certified (encoded : EncodedJson) :
    JsonEncoding encoded.value encoded.detach.get := encoded.certified

def EncodedJson.native (value : Lean.Json) : EncodedJson :=
  ⟨Thunk.pure value, Thunk.mk fun _ => [value.compress], JsonEncoding.native value⟩

def EncodedJson.snapshot (source : SourceSnapshot kind) : EncodedJson :=
  let rendering := source.encoding
  ⟨Thunk.pure source.value, Thunk.mk fun _ => [rendering.get.val],
    by
      change JsonEncoding source.value [source.wire]
      rw [source.encoded]
      exact JsonEncoding.native source.value⟩

private theorem fragments (items : List EncodedJson) :
    JsonFragments (items.map (·.value)) (items.map (·.chunks)) := by
  induction items with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.certified ih

def EncodedJson.array (items : List EncodedJson) : EncodedJson :=
  let renderings := items.map (·.rendering)
  let semantics := items.map (·.semantic)
  ⟨Thunk.mk (fun _ => .arr (semantics.map Thunk.get).toArray), Thunk.mk fun _ =>
    ["["] ++ ((renderings.map Thunk.get).intersperse [","]).flatten ++ ["]"],
      by simpa only [Thunk.get, semantics, renderings, List.map_map, Function.comp_def, EncodedJson.chunks, EncodedJson.value] using
        JsonEncoding.array _ _ (fragments items)⟩

def EncodedJson.object (fields : List (String × EncodedJson))
    (unique : (fields.map Prod.fst).Nodup) : EncodedJson :=
  let keys := fields.map Prod.fst
  let children := fields.map Prod.snd
  let renderings := children.map (·.rendering)
  let semantics := children.map (·.semantic)
  ⟨Thunk.mk (fun _ => Lean.Json.mkObj (keys.zip (semantics.map Thunk.get))), Thunk.mk fun _ =>
    ["{"] ++ (((keys.zip (renderings.map Thunk.get)).map fun (key, wire) =>
       [(Lean.Json.str key).compress, ":"] ++ wire).intersperse [","]).flatten ++ ["}"],
      by simpa only [Thunk.get, semantics, renderings, List.map_map, Function.comp_def, EncodedJson.chunks, EncodedJson.value] using
        JsonEncoding.object _ _ _ (by simp [children]) unique (fragments children)⟩

/-- Canonical key order and last-key ownership are shared by semantic and native
projections. Semantic object trees are only constructed if explicitly requested. -/
def EncodedJson.canonicalObject (fields : List (String × EncodedJson)) : EncodedJson :=
  let keys := fields.map Prod.fst
  let children := fields.map Prod.snd
  let semantics := children.map (·.semantic)
  let renderings := children.map (·.rendering)
  ⟨Thunk.mk (fun _ => Lean.Json.mkObj (keys.zip (semantics.map Thunk.get))),
    Thunk.mk (fun _ => canonicalChunks keys (renderings.map Thunk.get)), by
      simpa only [Thunk.get, semantics, renderings, List.map_map, Function.comp_def,
        EncodedJson.chunks, EncodedJson.value] using
        JsonEncoding.canonicalObject keys (children.map (·.value)) (children.map (·.chunks))
          (by simp [keys, children]) (fragments children)⟩

/-- Batch bounded native leaf fields through Lean's single compression work queue.
This avoids one independent compressor and fragment list per field. The bounded
semantic object remains owned by this leaf; the complete catalog stays streamed. -/
def EncodedJson.nativeObject (fields : List (String × Lean.Json)) : EncodedJson :=
  EncodedJson.native (Lean.Json.mkObj fields)

theorem EncodedJson.nativeObject_value (fields : List (String × Lean.Json)) :
    (EncodedJson.nativeObject fields).value = Lean.Json.mkObj fields := rfl

/-- Group one bounded publisher fragment without retaining its semantic tree. -/
def EncodedJson.compact (encoded : EncodedJson) : EncodedJson :=
  let rendering := encoded.rendering
  ⟨encoded.semantic, Thunk.mk (fun _ => [String.join rendering.get]),
    JsonEncoding.compact encoded.certified⟩

theorem EncodedJson.compact_wire (encoded : EncodedJson) :
    encoded.compact.wire = encoded.wire := by
  simp [compact, wire, chunks, Thunk.get]

theorem EncodedJson.array_value (items : List EncodedJson) :
    (EncodedJson.array items).value = .arr (items.map (·.value)).toArray := by
  simp [array, value, Thunk.get, List.map_map, Function.comp_def]

private theorem zip_projections (fields : List (String × EncodedJson)) :
    (fields.map Prod.fst).zip (fields.map (fun field => field.2.value)) =
      fields.map (fun field => (field.1, field.2.value)) := by
  induction fields with
  | nil => rfl
  | cons head tail ih => simpa using congrArg (List.cons (head.1, head.2.value)) ih

theorem EncodedJson.canonicalObject_value (fields : List (String × EncodedJson)) :
    (EncodedJson.canonicalObject fields).value =
      Lean.Json.mkObj (fields.map fun (key, encoded) => (key, encoded.value)) := by
  simp only [canonicalObject, value, Thunk.get, List.map_map, Function.comp_def]
  exact congrArg Lean.Json.mkObj (zip_projections fields)

end CedarPooSpec.Transport
