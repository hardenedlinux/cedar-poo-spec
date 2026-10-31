import CedarPooSpec.Transport.SourceCatalog

namespace CedarPooSpec.Transport.SourceTableTest
open LeanPoo.Functional.ObjectContract

def initial : SourcePool .policy := {}
def sample : Lean.Json := Lean.Json.mkObj [("source", Lean.toJson "full policy")]

theorem arbitrary_source_bound (pool : SourcePool kind) (source : Lean.Json) :
    (pool.publish source).next.resolve (pool.publish source).reference = some source.compress :=
  pool.publish_bound source

theorem arbitrary_source_frame (pool : SourcePool kind) (source : Lean.Json)
    (index : Nat) (present : index < pool.entries.size) :
    (pool.publish source).next.entries[index]? = pool.entries[index]? :=
  pool.publish_frame source index present

theorem arbitrary_publication_contract (pool : SourcePool kind) (source : Lean.Json) :
    diagnose (sourceContract kind source.compress)
      ((pool.publish source).next, (pool.publish source).reference) = [] :=
  publication_contract pool source

-- Executable negative controls use the actual publisher and Contract.
#eval show IO Unit from do
  let first := initial.publish sample
  let hit := first.next.publish sample
  unless hit.reference.index == first.reference.index && hit.next.entries.size == 1 do
    throw (IO.userError "complete source reuse failed")
  let changed := hit.next.publish (Lean.toJson "different source")
  unless changed.next.entries.size == 2 do
    throw (IO.userError "changed source reused old reference")
  unless !(diagnose (sourceContract .policy sample.compress)
      (changed.next, changed.reference)).isEmpty do
    throw (IO.userError "forged source reference admitted")
  unless !(diagnose (sourceContract .policy sample.compress)
      (changed.next, ⟨999⟩)).isEmpty do
    throw (IO.userError "missing source reference admitted")
  IO.println "SOURCE-TABLE-CONTRACT-OK bound/frame/changed/missing/full-source"
theorem arbitrary_published_value (pool : SourcePool kind) (source : Lean.Json) :
    ((pool.publish source).next.entries[(pool.publish source).reference.index]?).map
      (fun snapshot => snapshot.value.compress) = some source.compress := publication_value pool source
#print axioms arbitrary_published_value
#print axioms arbitrary_source_bound
#print axioms arbitrary_source_frame
#print axioms arbitrary_publication_contract
end CedarPooSpec.Transport.SourceTableTest
