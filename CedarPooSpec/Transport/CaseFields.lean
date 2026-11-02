import CedarPooSpec.Transport.Case
import CedarPooSpec.Transport.Wire
import Std.Data.TreeMap.Raw.AdditionalOperations

/-! Fill one fixed Case-field layout through public tree-map operations. The
original list projection remains the exact semantic reference. -/
namespace CedarPooSpec.Transport
private structure RefFields where
  name : String
  revision : String
  identifiers : Lean.Json
  request : Lean.Json
  response : Cedar.Spec.Response
  policy : SourceRef .policy
  entities : SourceRef .entities
private def expected (fields : RefFields) : Lean.Json :=
  Lean.toJson (match fields.response.decision with | .allow => "allow" | .deny => "deny")
private def reasons (fields : RefFields) : Lean.Json := Lean.toJson fields.response.determiningPolicies.toList
private def errors (fields : RefFields) : Lean.Json := Lean.toJson fields.response.erroringPolicies.toList
-- Scalar selectors avoid an indirect closure call and closure reference traffic
-- at every mapped node while retaining one typed, proof-bound field inventory.
private inductive Field where
  | name | revision | identifiers | request | expected | reasons | errors | policy | entities
@[inline] private def project (f : RefFields) : Field → Lean.Json
  | .name => Lean.toJson f.name
  | .revision => Lean.toJson f.revision
  | .identifiers => f.identifiers
  | .request => f.request
  | .expected => expected f
  | .reasons => reasons f
  | .errors => errors f
  | .policy => Lean.toJson f.policy.index
  | .entities => Lean.toJson f.entities.index
private def projections : List (String × Field) :=
  [("name", .name), ("revision", .revision), ("policy_ids", .identifiers),
    ("request", .request), ("expected", .expected), ("expected_reasons", .reasons),
    ("expected_error_policies", .errors), ("policy_ref", .policy), ("entities_ref", .entities)]
private def layout : Std.TreeMap.Raw String Field := .ofList projections
private def reference (fields : RefFields) : List (String × Lean.Json) :=
  projections.map fun (name, field) => (name, project fields field)
private def fast (f : RefFields) : Lean.Json := .obj (layout.map fun _ field => project f field)
private theorem exact_reference (f : RefFields) : fast f = Lean.Json.mkObj (reference f) := by rfl
open LeanPoo.Functional.ObjectContract
private def names : List String := projections.map Prod.fst
/-- Inventory/uniqueness Contract; complete field values are bound separately
by the exact reference theorem and the private constructor certificate. -/
def caseFieldInventory : Contract (List (String × Lean.Json)) String Lean.Json String where
  view := {
    isObject := fun _ => true
    prototype := fun _ => true
    names := fun fields => fields.map Prod.fst
    lookup := fun fields key => fields.lookup key }
  fields := names.map fun name => { name := name, check := fun _ _ => [] }
  strict := true
  constraints := []
  obligations := fun fields path => if (fields.map Prod.fst).Nodup then [] else [.rejected path "duplicate field"]
  validInventory := .inl rfl
private theorem inventory_bound (f : RefFields) : diagnose caseFieldInventory (reference f) = [] := by
  simp [diagnose, caseFieldInventory, reference, names, projections, extras, required,
    LeanPoo.Functional.ObjectDiagnostics.andThen, LeanPoo.Functional.ObjectDiagnostics.all, List.lookup]

-- This certificate is consumed by the native publisher. Both the reference list
-- and Contract diagnostics occur only in erased proofs, not per-case execution.
private def RefFields.encode (fields : RefFields) :
    { encoded : EncodedJson //
      diagnose caseFieldInventory (reference fields) = [] ∧
      encoded.value = Lean.Json.mkObj (reference fields) } :=
  ⟨EncodedJson.native (fast fields), inventory_bound fields, exact_reference fields⟩

/-- All manifest/evolution Cases share this typed field constructor. Source refs
retain their kind indices and request serialization fails at its original point. -/
def Case.encodedFields (input : Case) (policy : SourceRef .policy)
    (entities : SourceRef .entities) : Except String EncodedJson := do
  let request ← (PolicyJson.request input.request).mapError reprStr
  let fields : RefFields := {
    name := input.name, revision := input.revision
    identifiers := input.policy.identifiers.get.val
    request := request, response := input.response.get
    policy := policy, entities := entities }
  return fields.encode.val

/-- Exact original field object, including every value and source-reference kind. -/
theorem Case.encodedFields_value (input : Case) (policy : SourceRef .policy)
    (entities : SourceRef .entities) :
    (input.encodedFields policy entities).map (·.value) =
      input.fields.map (fun fields => Lean.Json.mkObj (fields ++ [
        ("policy_ref", Lean.toJson policy.index), ("entities_ref", Lean.toJson entities.index)])) := by
  unfold Case.encodedFields Case.fields
  cases PolicyJson.request input.request <;> rfl

end CedarPooSpec.Transport
