import Lean.Data.Json
import Std.Data.HashMap
import LeanPoo.Functional.ObjectContract

/-! Kind-indexed immutable source publication. Hashes only find candidates;
complete encoded source equality and proof-bearing references bind publication. -/
namespace CedarPooSpec.Transport
inductive SourceKind where | policy | entities | schema
  deriving Repr, DecidableEq
structure SourceRef (kind : SourceKind) where
  index : Nat
  deriving Repr
structure Snapshot (kind : SourceKind) where
  value : Lean.Json
  wire : String
  encoded : wire = value.compress
structure SourcePool (kind : SourceKind) where
  entries : Array (Snapshot kind) := #[]
  candidates : Std.HashMap String Nat := {}

def SourcePool.resolve (pool : SourcePool kind) (ref : SourceRef kind) : Option String :=
  (pool.entries[ref.index]?).map (·.wire)
structure Publication (before : SourcePool kind) (source : Lean.Json) where
  next : SourcePool kind
  reference : SourceRef kind
  bound : next.resolve reference = some source.compress
  frame : ∀ i, i < before.entries.size → next.entries[i]? = before.entries[i]?

private def append (pool : SourcePool kind) (source : Lean.Json) : Publication pool source where
  next := ⟨pool.entries.push ⟨source, source.compress, rfl⟩,
    pool.candidates.insert source.compress pool.entries.size⟩
  reference := ⟨pool.entries.size⟩
  bound := by simp [SourcePool.resolve]
  frame := by
    intro i h
    simp only [Array.getElem?_push, show i ≠ pool.entries.size from Nat.ne_of_lt h, ite_false]

def SourcePool.publish (pool : SourcePool kind) (source : Lean.Json) : Publication pool source :=
  match pool.candidates[source.compress]? with
  | some index =>
      if bound : pool.resolve ⟨index⟩ = some source.compress then
        ⟨pool, ⟨index⟩, bound, fun _ _ => rfl⟩
      else append pool source
  | none => append pool source

theorem SourcePool.publish_bound (pool : SourcePool kind) (source : Lean.Json) :
    (pool.publish source).next.resolve (pool.publish source).reference = some source.compress :=
  (pool.publish source).bound

theorem SourcePool.publish_frame (pool : SourcePool kind) (source : Lean.Json)
    (i : Nat) (existsBefore : i < pool.entries.size) :
    (pool.publish source).next.entries[i]? = pool.entries[i]? :=
  (pool.publish source).frame i existsBefore

/-- Published JSON values, not merely cached lookup keys, retain full source bytes. -/
theorem publication_value (pool : SourcePool kind) (source : Lean.Json) :
    ((pool.publish source).next.entries[(pool.publish source).reference.index]?).map
      (fun snapshot => snapshot.value.compress) = some source.compress := by
  cases entry : (pool.publish source).next.entries[(pool.publish source).reference.index]? with
  | none => simpa [SourcePool.resolve, entry] using (pool.publish source).bound
  | some snapshot =>
    simpa [SourcePool.resolve, entry, snapshot.encoded] using (pool.publish source).bound

open LeanPoo.Functional.ObjectContract
/-- The actual reference object view resolves through its kind-indexed pool.
Recognition checks full source bytes, not an ID, digest or observed decision. -/
def sourceContract (kind : SourceKind) (expected : String) :
    Contract (SourcePool kind × SourceRef kind) String String String where
  view := {
    isObject := fun _ => true
    prototype := fun _ => true
    names := fun _ => ["source"]
    lookup := fun pair key => if key = "source" then pair.1.resolve pair.2 else none }
  fields := [{ name := "source", check := fun actual path =>
    if actual = expected then [] else [.rejected path "source mismatch"] }]
  strict := true
  constraints := []
  obligations := fun _ _ => []
  validInventory := .inl rfl

theorem publication_contract (pool : SourcePool kind) (source : Lean.Json) :
    diagnose (sourceContract kind source.compress)
      ((pool.publish source).next, (pool.publish source).reference) = [] := by
  simp [diagnose, sourceContract, extras, required, (pool.publish source).bound,
    LeanPoo.Functional.ObjectDiagnostics.andThen, LeanPoo.Functional.ObjectDiagnostics.all]
end CedarPooSpec.Transport
