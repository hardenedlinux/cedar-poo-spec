import CedarPooSpec.Functional.Compilation
import CedarPooSpec.Authorization.Compound

/-!
A typed operation projects the effect and observed state into Cedar's request
model. The projection is fixed when the operation is constructed; a later Host
must still authenticate the actual effect and state before execution.
-/

namespace CedarPooSpec.Admission

open Cedar.Spec CedarPooSpec.PolicyModules

structure BoundOperation (Effect State : Type)
    (project : Effect → State → Request) where
  effect : Effect
  state : State

def BoundOperation.request {Effect State : Type}
    {project : Effect → State → Request}
    (operation : BoundOperation Effect State project) : Request :=
  project operation.effect operation.state

/-- Check a concrete operation against the actual effect and state supplied
    by the caller. This equality check does not authenticate either input. -/
def BoundOperation.matches {Effect State : Type}
    {project : Effect → State → Request}
    [DecidableEq Effect] [DecidableEq State]
    (operation : BoundOperation Effect State project)
    (effect : Effect) (state : State) : Bool :=
  decide (operation.effect = effect ∧ operation.state = state)

/-- A value mismatch is distinct from Cedar compilation or evaluation failure. -/
inductive Error where
  | effectMismatch
  | stateMismatch
  | policy (error : PolicyModules.Error)
  deriving Repr, BEq

/-- Compare the values supplied at admission with the bound operation before
    reusing the proof-bearing Cedar evaluation of its request. The Host must
    authenticate those values and bind any eventual execution to them. -/
def BoundOperation.authorize {Effect State : Type}
    {project : Effect → State → Request}
    [DecidableEq Effect] [DecidableEq State]
    (operation : BoundOperation Effect State project)
    (effect : Effect) (state : State)
    (model : Model) (root : String) (entities : Entities) :
    Except Error
      (Authorization.Compound.Receipt model root [operation.request] entities) :=
  if !decide (operation.effect = effect) then
    .error .effectMismatch
  else if !decide (operation.state = state) then
    .error .stateMismatch
  else
    ((CedarPooSpec.Functional.compilation model).authorize root [operation.request] entities).mapError .policy

end CedarPooSpec.Admission
