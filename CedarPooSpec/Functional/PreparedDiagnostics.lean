import LeanPoo.Functional.ObjectContract

/-! Stage immutable Contract descriptor work without caching object admission.
The prepared report is indexed by, and pointwise equal to, the original Contract. -/
namespace CedarPooSpec.Functional
open LeanPoo.Functional ObjectContract ObjectDiagnostics

structure PreparedDiagnostics [DecidableEq Key] (contract : Contract Carrier Key Value Detail) where
  report : Carrier → List (Issue Key Detail)
  aligned : ∀ value, report value = diagnose contract value []

/-- Fuse declared-name membership and root-path callback traversal without transient maps.
Structural checks, refusal order, constraints and obligations retain POO semantics. -/
def prepareDiagnostics [DecidableEq Key] (contract : Contract Carrier Key Value Detail) :
    PreparedDiagnostics contract :=
  let inventory := fun value => if contract.strict then
    (contract.view.names value).filterMap fun name =>
      if contract.fields.any (fun field => decide (field.name = name)) then none
      else some (Issue.unknownField [name])
    else []
  { report := fun value =>
      if !contract.view.isObject value then [.expectedObject []]
      else if !contract.view.prototype value then [.prototypeMismatch []]
      else andThen (fun value => inventory value ++ required contract value [])
        (andThen (fun value => contract.constraints.flatMap (fun check => check value []))
          (fun value => contract.obligations value [])) value
    aligned := by
      intro value
      simp [inventory, diagnose, extras, ObjectDiagnostics.all, List.flatMap_map,
        List.any_eq_true, List.mem_map] }

theorem prepareDiagnostics_exact [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (value : Carrier) : (prepareDiagnostics contract).report value = diagnose contract value [] :=
  (prepareDiagnostics contract).aligned value
end CedarPooSpec.Functional
