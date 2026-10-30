import CedarPooSpec.Gateway.Admission
import CedarPooSpec.Functional.ObjectProfile
import LeanPoo.Object.Dataflow

/-! Gateway governance objects use the existing source-bound C4/Dataflow owner.
Records hold immutable values/proofs; inheritance belongs to these actual typed
objects. The original profile is an external admitted commitment, never a slot a
child can override to justify weakening itself. -/
namespace CedarPooSpec.Gateway

def Profile.Refines (original current : Profile) : Prop :=
  original.valid = true ∧ current.valid = true ∧ current.identity = original.identity ∧
    original.requiredChecks.Sublist current.requiredChecks

instance (original current : Profile) : Decidable (original.Refines current) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem Profile.Refines.trans {original middle current : Profile}
    (first : original.Refines middle) (second : middle.Refines current) :
    original.Refines current :=
  ⟨first.1, second.2.1, second.2.2.1.trans first.2.2.1, first.2.2.2.trans second.2.2.2⟩

namespace ProfileObject
open LeanPoo.Object.Dataflow (Expr)
open LeanPoo.Functional.ObjectContract

inductive Key where
  | identity | checks | profile
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Repr

abbrev Value : Key → Type
  | .identity => String
  | .checks => List String
  | .profile => Profile

abbrev Object := LeanPoo.Object.Dataflow.Instance Key Value

def define (name : String) (initial : Profile) :
    Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  LeanPoo.Object.Dataflow.define name do
    LeanPoo.Object.Dataflow.Builder.value .identity initial.identity
    LeanPoo.Object.Dataflow.Builder.value .checks initial.requiredChecks
    LeanPoo.Object.Dataflow.Builder.derived .profile
      (Profile.mk <$> Expr.need (Value := Value) .identity <*> Expr.need (Value := Value) .checks)

/-- Extend the inherited check method, not a materialized copy of its output.
The inherited profile expression observes final-self checks through Expr.need. -/
def extendChecks (parent : Object) (name : String) (additional : List String) :
    Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  parent.extendWith name do
    LeanPoo.Object.Dataflow.Builder.field .checks
      (.extend (.pure fun _ => fun inherited => inherited.map (· ++ additional)))

private def shape : Functional.ObjectProfile.Check Key Value :=
  Functional.ObjectProfile.shape [.identity, .checks, .profile]

private def refinement (original : Profile) (object : Object) (path : List Key) :
    List (Issue Key String) :=
  match object.read .profile with
  | none => [.rejected path "missing Gateway profile"]
  | some current =>
    if original.Refines current ∧ object.read .identity = some current.identity ∧
        object.read .checks = some current.requiredChecks then []
    else [.rejected path "Gateway profile weakens or substitutes the original contract"]

/-- Ordinary POO inheritance permits overrides. This explicit strengthening
Contract refuses removed/reordered original obligations and substituted fields. -/
def contract (original : Profile) : Functional.ObjectProfile.Check Key Value :=
  refine shape (refinement original)

abbrev Session (original : Profile) (object : Object) :=
  Functional.ObjectProfile.Session (contract original)
    (Functional.ObjectProfile.factory (contract original)) object

def openSession (original : Profile) (object : Object) :
    Except (List (Issue Key String)) (Session original object) :=
  Functional.ObjectProfile.Session.open (contract original)
    (Functional.ObjectProfile.factory (contract original)) object

theorem read_preserves_original_requirements
    (session : Session original object) (current : Profile)
    (found : session.read .profile = some current) : original.Refines current := by
  have accepted := session.access.accepted
  have actual := Functional.ObjectProfile.Access.read_matches session.access .profile current found
  have checked := (refine_accepts_iff shape (refinement original) object []).mp accepted
  have semantic := checked.2
  simp only [refinement, actual] at semantic
  split at semantic
  · rename_i agreement
    exact agreement.1
  · simp at semantic

/-- Compose actual object projection and message admission: every inherited
original check has a satisfied named assessment. This proves labels, not the
truth of an external budget/history service's response. -/
theorem inherited_obligations_are_satisfied
    (session : Session original object) (current : Profile)
    (found : session.read .profile = some current) (checks : List Assessment)
    (accepted : current.accepts checks = true) :
    ∀ name ∈ original.requiredChecks,
      ∃ assessment ∈ checks, assessment.name = name ∧ assessment.status = .satisfied := by
  intro name member
  have currentMember := (read_preserves_original_requirements session current found).2.2.2.subset member
  have names := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).2).2
  have sameNames := of_decide_eq_true names
  rw [← sameNames] at currentMember
  obtain ⟨assessment, present, sameName⟩ := List.mem_map.mp currentMember
  exact ⟨assessment, present, sameName, accepted_assessments_are_satisfied current checks accepted assessment present⟩

/-- The caller retains this source/factory-indexed Session. Host publication
must bind its actual source closure and original commitment, not just its name. -/
def prepareFromObject {E S : Type} (model : PolicyModules.Model) (root : String)
    (schema : Cedar.Validation.Schema) (context : Context)
    (session : Session original object) (project : E → S → Cedar.Spec.Request)
    (effect : E) (state : S) : Except Error (Prepared E S project) := do
  let profile ← (session.read .profile).elim (.error Error.invalidProfile) Except.ok
  prepare model root schema context profile project effect state

end ProfileObject
end CedarPooSpec.Gateway
