import CedarPooSpec.Attackers.Trace
import CedarPooSpec.Functional.ObjectProfile

/-! LeanPoo attacker objects share typed slots and cooperative C4 extensions
across verticals. The authoritative base is a type index. A selected descendant
must retain the independently required parent's actual model, not just its name.
Goals name verification obligations; labels never grant runtime authority. -/
namespace CedarPooSpec.Attackers.ProfileObject
open LeanPoo.Object.Dataflow (Expr)
open LeanPoo.Functional.ObjectContract
variable {Capability : Type} [DecidableEq Capability]

structure Model (Capability : Type) where
  initial : List Capability
  rules : List (Rule Capability)
  isolated : List Capability
  goals : List String
  deriving DecidableEq, Repr

def Model.valid (model : Model Capability) : Bool :=
  decide (model.initial.Nodup ∧ model.rules.Nodup ∧ model.isolated.Nodup ∧
    model.goals ≠ [] ∧ model.goals.Nodup ∧
    ∀ cap ∈ model.isolated, cap ∉ model.initial ∧ ∀ rule ∈ model.rules, rule.grants ≠ cap) &&
    model.goals.all (fun goal => !goal.isEmpty)

/-- Adding an industry may not quietly remove attacker powers, existing goals
or declared independent boundaries. A changed threat premise needs a new base. -/
def Model.extends (child parent : Model Capability) : Bool :=
  decide ((∀ cap ∈ parent.initial, cap ∈ child.initial) ∧
    (∀ rule ∈ parent.rules, rule ∈ child.rules) ∧
    (∀ cap ∈ parent.isolated, cap ∈ child.isolated) ∧
    (∀ goal ∈ parent.goals, goal ∈ child.goals))

structure Certified (required : Model Capability) where
  model : Model Capability
  valid : model.valid = true
  retains : model.extends required = true

def certify (required model : Model Capability) : Option (Certified required) :=
  if checked : model.valid = true ∧ model.extends required = true then
    some ⟨model, checked.1, checked.2⟩ else none

variable {required : Model Capability}

inductive Key where
  | initial | rules | isolated | goals | model
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Repr

abbrev Value (required : Model Capability) : Key → Type
  | .initial | .isolated => List Capability
  | .rules => List (Rule Capability)
  | .goals => List String
  | .model => Option (Certified required)

abbrev Object (required : Model Capability) := LeanPoo.Object.Dataflow.Instance Key (Value required)

def define (name : String) (required : Model Capability) :
    Except (LeanPoo.Object.Dataflow.Error Key) (Object required) :=
  LeanPoo.Object.Dataflow.define name do
    LeanPoo.Object.Dataflow.Builder.value .initial required.initial
    LeanPoo.Object.Dataflow.Builder.value .rules required.rules
    LeanPoo.Object.Dataflow.Builder.value .isolated required.isolated
    LeanPoo.Object.Dataflow.Builder.value .goals required.goals
    LeanPoo.Object.Dataflow.Builder.derived .model
      ((fun initial rules isolated goals => certify required ⟨initial, rules, isolated, goals⟩)
        <$> Expr.need (Value := Value required) .initial
        <*> Expr.need (Value := Value required) .rules
        <*> Expr.need (Value := Value required) .isolated
        <*> Expr.need (Value := Value required) .goals)

/-- Cooperative `.extend` retains sibling contributions under C4 composition. -/
def derive (parent : Object required) (name : String) (parents : List String) (extra : Model Capability) :
    Except (LeanPoo.Object.Dataflow.Error Key) (Object required) :=
  parent.defineWith name parents do
    LeanPoo.Object.Dataflow.Builder.field .initial
      (.extend (.pure fun _ previous => previous.map (· ++ extra.initial)))
    LeanPoo.Object.Dataflow.Builder.field .rules
      (.extend (.pure fun _ previous => previous.map (· ++ extra.rules)))
    LeanPoo.Object.Dataflow.Builder.field .isolated
      (.extend (.pure fun _ previous => previous.map (· ++ extra.isolated)))
    LeanPoo.Object.Dataflow.Builder.field .goals
      (.extend (.pure fun _ previous => previous.map (· ++ extra.goals)))

def augment (parent : Object required) (name : String) (extra : Model Capability) :
    Except (LeanPoo.Object.Dataflow.Error Key) (Object required) :=
  derive parent name [parent.plan.root] extra

/-- Shared-base diamonds remain in one source family, with one declaration
owner. Independent graph merging must not duplicate the shared root. -/
def mix (family : Object required) (name : String) (parents : List String) :
    Except (LeanPoo.Object.Dataflow.Error Key) (Object required) :=
  family.defineWith name parents (pure ⟨⟩)

def contract (required : Model Capability) : Functional.ObjectProfile.Check Key (Value required) :=
  refine (Functional.ObjectProfile.shape [.initial, .rules, .isolated, .goals, .model]) fun object path =>
    match object.read .initial, object.read .rules, object.read .isolated,
        object.read .goals, object.read .model with
    | some initial, some rules, some isolated, some goals, some (some selected) =>
        if decide (selected.model = ⟨initial, rules, isolated, goals⟩) then []
        else [.rejected path "attacker model does not match inherited slots"]
    | _, _, _, _, _ => [.rejected path "invalid or incomplete attacker model"]

abbrev Session (required : Model Capability) (object : Object required) :=
  Functional.ObjectProfile.Session (contract required)
    (Functional.ObjectProfile.factory (contract required)) object

def openSession (required : Model Capability) (object : Object required) :
    Except (List (Issue Key String)) (Session required object) :=
  Functional.ObjectProfile.Session.open (contract required)
    (Functional.ObjectProfile.factory (contract required)) object

variable {parentObject selectedObject : Object required}

structure Selection (parent : Session required parentObject) (selected : Session required selectedObject) where
  parentModel : Certified required
  selectedModel : Certified required
  parentRead : parent.read .model = some (some parentModel)
  selectedRead : selected.read .model = some (some selectedModel)
  retainsParent : selectedModel.model.extends parentModel.model = true

def selectSessions (parent : Session required parentObject) (selected : Session required selectedObject) :
    Option (Selection parent selected) :=
  match parentRead : parent.read .model, selectedRead : selected.read .model with
  | some (some parentModel), some (some selectedModel) =>
      if retained : selectedModel.model.extends parentModel.model = true then
        some ⟨parentModel, selectedModel, parentRead, selectedRead, retained⟩
      else none
  | _, _ => none

variable {parent : Session required parentObject} {selected : Session required selectedObject}

theorem selection_retains_actual_parent (selection : Selection parent selected) :
    parentObject.read .model = some (some selection.parentModel) ∧
    selectedObject.read .model = some (some selection.selectedModel) ∧
    selection.selectedModel.model.extends selection.parentModel.model = true ∧
    selection.selectedModel.model.extends required = true :=
  ⟨parent.read_matches .model _ selection.parentRead,
    selected.read_matches .model _ selection.selectedRead,
    selection.retainsParent, selection.selectedModel.retains⟩

def Certified.surface (certified : Certified required)
    (reachable : List Capability → Request → Bool)
    (invoke : World → Request → Option (World × Output)) : Surface Capability Request World Output :=
  { rules := certified.model.rules, reachable, invoke }

def Certified.initialState (certified : Certified required) (world : World) : State Capability World Output :=
  { known := certified.model.initial, world }

/-- The capability invariant is obtained from the actual object's certified
slots, rather than a second hand-maintained rule list in each vertical. -/
theorem certified_isolation (certified : Certified required)
    (reachable : List Capability → Request → Bool)
    (invoke : World → Request → Option (World × Output)) (world : World)
    (cap : Capability) (isolated : cap ∈ certified.model.isolated)
    (actions : List (Action Capability Request)) :
    cap ∉ (run (certified.surface reachable invoke) (certified.initialState world) actions).known := by
  have valid := (Bool.and_eq_true_iff.mp certified.valid).1
  have roots := (of_decide_eq_true valid).2.2.2.2.2
  have boundary := roots cap isolated
  exact run_preserves_absence _ cap boundary.2 _ boundary.1 actions

end CedarPooSpec.Attackers.ProfileObject
