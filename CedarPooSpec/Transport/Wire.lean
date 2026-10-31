import CedarPooSpec.Transport.SourceTable

/-! Compositional JSON framing over complete, certified native fragments.
The certificate binds every embedded fragment to its actual JSON value. -/
namespace CedarPooSpec.Transport

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
  value : Lean.Json
  rendering : Thunk { chunks : List String // JsonEncoding value chunks }

def EncodedJson.chunks (encoded : EncodedJson) : List String := encoded.rendering.get.val
def EncodedJson.wire (encoded : EncodedJson) : String := String.join encoded.chunks
theorem EncodedJson.certified (encoded : EncodedJson) :
    JsonEncoding encoded.value encoded.chunks := encoded.rendering.get.property
theorem EncodedJson.wire_eq (encoded : EncodedJson) :
    encoded.wire = String.join encoded.chunks := rfl

def EncodedJson.native (value : Lean.Json) : EncodedJson :=
  ⟨value, Thunk.mk fun _ => ⟨[value.compress], JsonEncoding.native value⟩⟩

def EncodedJson.snapshot (source : SourceSnapshot kind) : EncodedJson :=
  ⟨source.value, Thunk.mk fun _ => ⟨[source.wire],
    by simpa only [source.encoded] using JsonEncoding.native source.value⟩⟩

private theorem fragments (items : List EncodedJson) :
    JsonFragments (items.map (·.value)) (items.map (·.chunks)) := by
  induction items with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.certified ih

def EncodedJson.array (items : List EncodedJson) : EncodedJson :=
  ⟨.arr (items.map (·.value)).toArray, Thunk.mk fun _ =>
    ⟨["["] ++ ((items.map (·.chunks)).intersperse [","]).flatten ++ ["]"],
      JsonEncoding.array _ _ (fragments items)⟩⟩

def EncodedJson.object (fields : List (String × EncodedJson))
    (unique : (fields.map Prod.fst).Nodup) : EncodedJson :=
  let keys := fields.map Prod.fst
  let children := fields.map Prod.snd
  ⟨Lean.Json.mkObj (keys.zip (children.map (·.value))), Thunk.mk fun _ =>
    ⟨["{"] ++ (((keys.zip (children.map (·.chunks))).map fun (key, wire) =>
       [(Lean.Json.str key).compress, ":"] ++ wire).intersperse [","]).flatten ++ ["}"],
      JsonEncoding.object _ _ _ (by simp [keys, children]) unique (fragments children)⟩⟩

end CedarPooSpec.Transport
