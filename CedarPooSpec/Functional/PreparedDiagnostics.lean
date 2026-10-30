import LeanPoo.Functional.ObjectContract

/-! Stage immutable Contract descriptor work without caching object admission.
The prepared report is indexed by, and pointwise equal to, the original Contract. -/
namespace CedarPooSpec.Functional
open LeanPoo.Functional ObjectContract ObjectDiagnostics
variable {Carrier Key Value Detail : Type}

structure PreparedDiagnostics [DecidableEq Key] (contract : Contract Carrier Key Value Detail) where
  report : Carrier → List (Issue Key Detail)
  aligned : ∀ value, report value = diagnose contract value []

-- Root-path traversals use ordinary recursion instead of allocating callback
-- closures for every object and inventory name. No descriptor list is staged.
private def declared [DecidableEq Key] (fields : List (Field Key Value Detail))
    (name : Key) : Bool :=
  match fields with
  | [] => false
  | field :: rest => if field.name = name then true else declared rest name

private theorem declared_eq [DecidableEq Key] (fields : List (Field Key Value Detail))
    (name : Key) : declared fields name = fields.any (fun field => decide (field.name = name)) := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp [declared, ih]

private def inventoryRoot [DecidableEq Key] (fields : List (Field Key Value Detail)) :
    List Key → List (Issue Key Detail)
  | [] => []
  | name :: rest => if declared fields name then inventoryRoot fields rest
      else .unknownField [name] :: inventoryRoot fields rest

private theorem inventoryRoot_eq [DecidableEq Key] (fields : List (Field Key Value Detail))
    (names : List Key) : inventoryRoot fields names = names.filterMap (fun name =>
      if fields.any (fun field => decide (field.name = name)) then none
      else some (Issue.unknownField [name])) := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp [inventoryRoot, declared_eq, List.filterMap_cons, ih]; split <;> rfl

private def requiredRoot (fields : List (Field Key Value Detail))
    (lookup : Carrier → Key → Option Value) (value : Carrier) : List (Issue Key Detail) :=
  match fields with
  | [] => []
  | field :: rest =>
    (match lookup value field.name with
      | none => [.missingField [field.name]]
      | some item => field.check item [field.name]) ++ requiredRoot rest lookup value

private theorem requiredRoot_eq (fields : List (Field Key Value Detail))
    (lookup : Carrier → Key → Option Value) (value : Carrier) :
    requiredRoot fields lookup value = fields.flatMap (fun field =>
      match lookup value field.name with
      | none => [.missingField [field.name]]
      | some item => field.check item [field.name]) := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp [requiredRoot, List.flatMap_cons, ih]

private def constraintsRoot (checks : List (Carrier → List Key → List (Issue Key Detail)))
    (value : Carrier) : List (Issue Key Detail) :=
  match checks with
  | [] => []
  | check :: rest => check value [] ++ constraintsRoot rest value

private theorem constraintsRoot_eq (checks : List (Carrier → List Key → List (Issue Key Detail)))
    (value : Carrier) : constraintsRoot checks value = checks.flatMap (fun check => check value []) := by
  induction checks with
  | nil => rfl
  | cons check rest ih => simp [constraintsRoot, List.flatMap_cons, ih]

/-- Fuse declared-name membership and root-path callback traversal without transient maps.
Structural checks, refusal order, constraints and obligations retain POO semantics. -/
def prepareDiagnostics [DecidableEq Key] (contract : Contract Carrier Key Value Detail) :
    PreparedDiagnostics contract :=
  let inventory := fun value => if contract.strict then
    inventoryRoot contract.fields (contract.view.names value) else []
  { report := fun value =>
      if !contract.view.isObject value then [.expectedObject []]
      else if !contract.view.prototype value then [.prototypeMismatch []]
      else andThen (fun value => inventory value ++ requiredRoot contract.fields contract.view.lookup value)
        (andThen (fun value => constraintsRoot contract.constraints value)
          (fun value => contract.obligations value [])) value
    aligned := by
      intro value
      simp [inventory, diagnose, extras, required, inventoryRoot_eq, requiredRoot_eq,
        constraintsRoot_eq, ObjectDiagnostics.all, List.flatMap_map,
        List.any_eq_true, List.mem_map] <;> rfl }

theorem prepareDiagnostics_exact [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (value : Carrier) : (prepareDiagnostics contract).report value = diagnose contract value [] :=
  (prepareDiagnostics contract).aligned value
end CedarPooSpec.Functional
