import CedarPooSpec.Scenarios.Functional

/-! Source-aware replay is a projection of the application's supplied events and
step function. It adds no attacker graph, policy evaluator or execution engine.
Reported source claims, assumptions and synthetic probes remain distinguishable. -/
namespace CedarPooSpec.Scenarios.Replay
open LeanPoo.Functional.DeclarativeMetadata

inductive Basis where
  | reported | assumed | probe
  deriving DecidableEq, Repr

structure Description where
  id : String
  title : String
  basis : Basis
  source : Option Nat := none
  atUTC : Option String := none
  limitation : String
  deriving DecidableEq, Repr

def Description.valid (metadata : Metadata) (stage : Description) : Bool :=
  !stage.id.isEmpty && !stage.title.isEmpty && !stage.limitation.isEmpty &&
    stage.atUTC.all (fun value => (Cedar.Spec.Ext.Datetime.parse value).isSome) &&
    match stage.basis with
    | .reported => stage.source.any (fun index => index < metadata.disclosures.length)
    | .assumed | .probe => stage.source.isNone && stage.atUTC.isNone

structure Stage (Event : Type) where
  description : Description
  events : List Event

def valid (metadata : Metadata) (stages : List (Stage Event)) : Bool :=
  metadata.valid && !stages.isEmpty &&
    decide ((stages.map (·.description.id)).Nodup) &&
    stages.all (fun stage => stage.description.valid metadata)

/-- Frames are computed from the actual fold of the supplied application step.
The display cannot choose a success/failure state independent of that execution. -/
def collect (step : State → Event → State) (summarize : State → Summary)
    (initial : State) : List (Stage Event) → List (Description × Summary)
  | [] => []
  | stage :: rest =>
      let after := stage.events.foldl step initial
      (stage.description, summarize after) :: collect step summarize after rest

variable {State Event Summary : Type} [DecidableEq Summary]

def contract (metadata : Metadata) (step : State → Event → State)
    (summarize : State → Summary) (initial : State) :
    Contract Unit (List (Stage Event)) (List (Description × Summary)) where
  input := ⟨"source-classified-replay-stages", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"actual-application-step-observations", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ stages result => valid metadata stages = true ∧
    result = collect step summarize initial stages
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (metadata : Metadata) (step : State → Event → State)
    (summarize : State → Summary) (initial : State) (stages : List (Stage Event)) :
    Except String (List (Description × Summary) × Unit) :=
  if valid metadata stages then .ok (collect step summarize initial stages, ())
  else .error "replay provenance refused"

theorem prepared_retains_execution {metadata : Metadata} {step : State → Event → State}
    {summarize : State → Summary} {initial : State} {stages : List (Stage Event)}
    (called : prepare metadata step summarize initial stages = .ok (result, ())) :
    valid metadata stages = true ∧ result = collect step summarize initial stages := by
  unfold prepare at called
  split at called
  · cases called; exact ⟨by assumption, rfl⟩
  · cases called

theorem invocation_retains_execution {metadata : Metadata} {step : State → Event → State}
    {summarize : State → Summary} {initial : State} {stages : List (Stage Event)}
    (receipt : Invocation (contract metadata step summarize initial)
      (prepare metadata step summarize initial) stages) :
    valid metadata stages = true ∧ receipt.result = collect step summarize initial stages := receipt.logic

end CedarPooSpec.Scenarios.Replay
