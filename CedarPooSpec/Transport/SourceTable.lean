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
/-- One immutable source value with one memoized full encoding. -/
structure SourceSnapshot (kind : SourceKind) where
  value : Lean.Json
  encoding : Thunk { wire : String // wire = value.compress }

def SourceSnapshot.ofJson (value : Lean.Json) : SourceSnapshot kind :=
  ⟨value, Thunk.mk fun _ => ⟨value.compress, rfl⟩⟩
def SourceSnapshot.wire (snapshot : SourceSnapshot kind) : String := snapshot.encoding.get.val
theorem SourceSnapshot.encoded (snapshot : SourceSnapshot kind) :
    snapshot.wire = snapshot.value.compress := snapshot.encoding.get.property

structure SourcePool (kind : SourceKind) where
  entries : Array (SourceSnapshot kind) := #[]
  candidates : Std.HashMap String Nat := {}
  recent : Option Nat := none

def SourcePool.resolve (pool : SourcePool kind) (ref : SourceRef kind) : Option String :=
  (pool.entries[ref.index]?).map (·.wire)
structure Publication (before : SourcePool kind) (source : Lean.Json) where
  next : SourcePool kind
  reference : SourceRef kind
  bound : next.resolve reference = some source.compress
  frame : ∀ i, i < before.entries.size → next.entries[i]? = before.entries[i]?

private def append (pool : SourcePool kind) (source : SourceSnapshot kind) :
    Publication pool source.value :=
  let index := pool.entries.size
  { next := { entries := pool.entries.push source
              candidates := pool.candidates.insert source.wire index
              recent := some index }
    reference := ⟨index⟩
    bound := by simp [SourcePool.resolve, index, source.encoded]
    frame := by
      intro i h
      simp only [Array.getElem?_push, show i ≠ pool.entries.size from Nat.ne_of_lt h, ite_false] }

/-- Typed publication reuses the snapshot's memoized encoding, including hits. -/
private def publishIndexed (pool : SourcePool kind) (source : SourceSnapshot kind) :
    Publication pool source.value :=
  let wire := source.wire
  match pool.candidates[wire]? with
  | some index =>
      if bound : pool.resolve ⟨index⟩ = some wire then
        ⟨{ pool with recent := some index }, ⟨index⟩,
          bound.trans (congrArg some source.encoded), fun _ _ => rfl⟩
      else append pool source
  | none => append pool source


/-- Consecutive Cases usually share one snapshot. Check the last published
reference before hashing the full wire again. Both hints remain untrusted:
every reuse resolves and compares complete source bytes in this exact pool. -/
def SourcePool.publishSnapshot (pool : SourcePool kind) (source : SourceSnapshot kind) :
    Publication pool source.value :=
  match pool.recent with
  | some index =>
      if bound : pool.resolve ⟨index⟩ = some source.wire then
        ⟨pool, ⟨index⟩, bound.trans (congrArg some source.encoded), fun _ _ => rfl⟩
      else publishIndexed pool source
  | none => publishIndexed pool source


/-- A checked consecutive-source hit leaves the publication inventory unchanged. -/
theorem SourcePool.publishSnapshot_recent (pool : SourcePool kind)
    (source : SourceSnapshot kind) (index : Nat)
    (recent : pool.recent = some index)
    (bound : pool.resolve ⟨index⟩ = some source.wire) :
    (pool.publishSnapshot source).next = pool ∧
      (pool.publishSnapshot source).reference.index = index := by
  simp [publishSnapshot, recent, bound]

def SourcePool.publish (pool : SourcePool kind) (source : Lean.Json) : Publication pool source :=
  pool.publishSnapshot (SourceSnapshot.ofJson source)

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
/-- The typed publisher used by the native catalog satisfies the actual Contract. -/
theorem publication_snapshot_contract (pool : SourcePool kind) (source : SourceSnapshot kind) :
    diagnose (sourceContract kind source.value.compress)
      ((pool.publishSnapshot source).next, (pool.publishSnapshot source).reference) = [] := by
  simp [diagnose, sourceContract, extras, required, (pool.publishSnapshot source).bound,
    LeanPoo.Functional.ObjectDiagnostics.andThen, LeanPoo.Functional.ObjectDiagnostics.all]

theorem publication_snapshot_value (pool : SourcePool kind) (source : SourceSnapshot kind) :
    ((pool.publishSnapshot source).next.entries[(pool.publishSnapshot source).reference.index]?).map
      (fun snapshot => snapshot.value.compress) = some source.value.compress := by
  cases entry : (pool.publishSnapshot source).next.entries[(pool.publishSnapshot source).reference.index]? with
  | none => simpa [SourcePool.resolve, entry] using (pool.publishSnapshot source).bound
  | some snapshot =>
    simpa [SourcePool.resolve, entry, snapshot.encoded] using (pool.publishSnapshot source).bound

end CedarPooSpec.Transport
