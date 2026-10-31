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

-- Streaming must stop at the first factory or publication error.
#eval show IO Unit from do
  let failed := CedarPooSpec.Transport.sourceCatalogFrom
    [("first", fun _ => .error "first factory"), ("later", fun _ => .error "later factory")]
  match failed with
  | .error "first factory" => pure ()
  | _ => throw (IO.userError "factory error order changed")
  let uid : Cedar.Spec.EntityUID := ⟨⟨"User", []⟩, "cycle"⟩
  let store : Cedar.Spec.Entities := Cedar.Data.Map.make [
    (uid, ⟨Cedar.Data.Map.empty, Cedar.Data.Set.make [uid], Cedar.Data.Map.empty⟩)]
  let req : Cedar.Spec.Request := ⟨uid, uid, uid, Cedar.Data.Map.empty⟩
  let source : CedarPooSpec.Transport.SourceSnapshot .policy :=
    CedarPooSpec.Transport.SourceSnapshot.ofJson
    (Lean.Json.mkObj [("staticPolicies", Lean.Json.mkObj []),
      ("templates", Lean.Json.mkObj []), ("templateLinks", Lean.toJson ([] : List Lean.Json))])
  let input : CedarPooSpec.Transport.Case := {
    name := "self-ancestor", revision := "source"
    policy := ⟨[], source, rfl⟩
    request := req, entities := store
    response := Thunk.mk fun _ => Cedar.Spec.isAuthorized req store []
    evaluated := rfl }
  let malformed := CedarPooSpec.Transport.sourceCatalogFrom
    [("first", fun _ => .ok (.manifest ⟨[input], none⟩)),
     ("later", fun _ => .error "later factory")]
  match malformed with
  | .error message =>
    if message == "later factory" then throw (IO.userError "publication error was deferred")
  | .ok _ => throw (IO.userError "malformed publication admitted")
  IO.println "SOURCE-CATALOG-FACTORY-OK first-factory/first-publication-error"

#print axioms CedarPooSpec.Transport.publication_snapshot_contract
#print axioms CedarPooSpec.Transport.publication_snapshot_value
#print axioms CedarPooSpec.Transport.Case.inline_projection
#print axioms CedarPooSpec.Transport.EntitySlot.read_value
#print axioms CedarPooSpec.Transport.EntitySlot.bound

-- The real composed encoder must escape keys/values and retain every fragment.
#eval show IO Unit from do
  let source : CedarPooSpec.Transport.SourceSnapshot .policy :=
    CedarPooSpec.Transport.SourceSnapshot.ofJson
    (Lean.Json.mkObj [("unicode", Lean.toJson "μ\nquoted\"")])
  let encoded := CedarPooSpec.Transport.EncodedJson.object [
    ("array", .array [.snapshot source, .native (.bool true), .native .null]),
    ("number", .native (Lean.toJson (17 : Nat))),
    ("text", .native (Lean.toJson "comma,colon:bracket]"))] (by simp)
  unless encoded.wire == encoded.value.compress do
    throw (IO.userError "certified canonical fragment wire differs")
  let unsorted := CedarPooSpec.Transport.EncodedJson.object [
    ("z", .snapshot source), ("a", .native (Lean.toJson "escaped"))] (by simp)
  unless (Lean.Json.parse unsorted.wire).toOption.map (·.compress) ==
      some unsorted.value.compress do
    throw (IO.userError "fragment value binding or key escaping failed")
  IO.println "CERTIFIED-JSON-FRAGMENTS-OK escaping/order/full-values"

#print axioms CedarPooSpec.PolicyPreparation.checkUsing_eq
#print axioms CedarPooSpec.PolicyModules.Model.compilePlan_graph
#print axioms CedarPooSpec.Transport.JsonFragments.length_eq
#print axioms CedarPooSpec.Transport.EncodedJson.certified
#print axioms LeanPoo.C4.Prepared.at_eq
#print axioms CedarPooSpec.PolicyModules.Model.compilePrepared_eq
#print axioms CedarPooSpec.PolicyModules.Model.compilePlanPrepared_eq
#print axioms LeanPoo.Object.compilePrepared_eq
#print axioms CedarPooSpec.Transport.EncodedJson.detach_eq
#print axioms CedarPooSpec.Transport.EncodedJson.detach_certified
