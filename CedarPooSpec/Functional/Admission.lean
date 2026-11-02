import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Admission.PolicySnapshot

/-! Bridge checked Functional policies to existing admission snapshots. The
caller supplies the current model/schema; no external freshness is inferred. -/
namespace CedarPooSpec.Functional

open Cedar.Spec Cedar.Validation CedarPooSpec.Admission

/-- Preserve the existing ticket representation, with the checked policy data. -/
def Ready.policySnapshot (ready : Ready context) : PolicySnapshot :=
  ⟨context.root, ready.checked.policies⟩

theorem Ready.policySnapshot_compiled (ready : Ready context) :
    context.model.compile ready.policySnapshot.root = .ok ready.policySnapshot.policies :=
  ready.checked.compiled

inductive RefreshError where
  | preparation (error : Error)
  | changed

/-- Checked current data, additionally bound to the complete ticket policy set. -/
abbrev Refreshed (model : PolicyModules.Model) (schema : Schema) (snapshot : PolicySnapshot) :=
  { ready : Ready ⟨model, snapshot.root, schema⟩ // ready.checked.policies = snapshot.policies }

/-- Re-prepare from a Program indexed by the caller's actual current model/schema.
Compare full policies, including order and bodies, before returning the witness.
An explicitly old Program remains an old snapshot, not an external freshness check. -/
def Program.refreshPolicy (program : Program model schema) (snapshot : PolicySnapshot) :
    Except RefreshError (Refreshed model schema snapshot) := do
  let ready ← (program.at snapshot.root).mapError .preparation
  if same : ready.checked.policies = snapshot.policies then return ⟨ready, same⟩
  else throw .changed

/-- A refreshed ticket really compiles under the supplied current model. -/
theorem Refreshed.compiled (current : Refreshed model schema snapshot) :
    model.compile snapshot.root = .ok snapshot.policies := by
  rw [← current.property]
  exact current.val.checked.compiled

/-- Current input decisions remain bound to the exact captured ticket policies. -/
theorem Refreshed.allowed_eq (current : Refreshed model schema snapshot)
    (requests : List Request) (entities : Entities) :
    (current.val.authorize requests entities).allowed =
      (!requests.isEmpty && (requests.map (fun request =>
        isAuthorized request entities snapshot.policies)).all (fun response =>
          response.decision == .allow && response.erroringPolicies.isEmpty)) := by
  rw [current.val.allowed_eq, current.property]

end CedarPooSpec.Functional
