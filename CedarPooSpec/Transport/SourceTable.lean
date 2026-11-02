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
/-- One complete key carries its already computed hash. Equality remains full
wire equality; the proof makes equal wires have equal hashes. -/
structure SourceKey where
  wire : String
  fingerprint : UInt64
  consistent : fingerprint = hash wire
instance : BEq SourceKey where
  beq left right := left.wire == right.wire
instance : LawfulBEq SourceKey where
  rfl := by
    intro value
    change (value.wire == value.wire) = true
    exact BEq.rfl
  eq_of_beq := by
    intro left right same
    have wires : left.wire = right.wire := eq_of_beq same
    rcases left with ⟨left, lh, lc⟩
    rcases right with ⟨right, rh, rc⟩
    dsimp at wires
    subst right
    cases lc
    cases rc
    rfl
instance : Hashable SourceKey where
  hash key := key.fingerprint

theorem SourceKey.hash_eq (left right : SourceKey) (same : left.wire = right.wire) :
    hash left = hash right := by
  change left.fingerprint = right.fingerprint
  exact left.consistent.trans ((congrArg (fun wire : String => hash wire) same).trans right.consistent.symm)

/-- Encoding and lookup preparation share one memoized result, not two thunks. -/
structure SourceSnapshot (kind : SourceKind) where
  value : Lean.Json
  encoding : Thunk { key : SourceKey // key.wire = value.compress }

def SourceSnapshot.ofJson (value : Lean.Json) : SourceSnapshot kind :=
  ⟨value, Thunk.mk fun _ =>
    let wire := value.compress
    ⟨⟨wire, hash wire, rfl⟩, rfl⟩⟩
def SourceSnapshot.wire (snapshot : SourceSnapshot kind) : String := snapshot.encoding.get.val.wire
theorem SourceSnapshot.encoded (snapshot : SourceSnapshot kind) :
    snapshot.wire = snapshot.value.compress := snapshot.encoding.get.property

theorem SourceSnapshot.fingerprint_bound (snapshot : SourceSnapshot kind) :
    snapshot.encoding.get.val.fingerprint = hash snapshot.wire :=
  snapshot.encoding.get.val.consistent

structure SourcePool (kind : SourceKind) where
  entries : Array (SourceSnapshot kind) := #[]
  candidates : Std.HashMap SourceKey Nat := {}
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
              candidates := pool.candidates.insert source.encoding.get.val index
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
  match pool.candidates[source.encoding.get.val]? with
  | some index =>
      if bound : pool.resolve ⟨index⟩ = some wire then
        ⟨{ pool with recent := some index }, ⟨index⟩,
          bound.trans (congrArg some source.encoded), fun _ _ => rfl⟩
      else append pool source
  | none => append pool source


/-- Consecutive Cases usually share one snapshot. Check the last published
reference before consulting the prepared key. Both hints remain untrusted:
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
