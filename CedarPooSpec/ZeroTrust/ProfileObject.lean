import CedarPooSpec.ZeroTrust.Continuous
import CedarPooSpec.Functional.ObjectProfile

/-! Optional POO interpretation of the functional framework. The original
requirement is a type index. A child may add requirements but cannot provide
a weaker profile without a proof of the original requirement. Host identity
and the choice of an authoritative original remain application obligations. -/
namespace CedarPooSpec.ZeroTrust.ProfileObject
open LeanPoo.Functional.ObjectContract

variable {E V : Type}

structure Profile (original : Requirement E V) where
  requirement : Requirement E V
  refines : Refines original requirement

variable {original : Requirement E V}

def Profile.strengthen (profile : Profile original) (extra : Requirement E V) : Profile original :=
  ⟨ZeroTrust.strengthen profile.requirement extra,
    refinement_trans profile.refines (strengthen_refines _ _)⟩

inductive Key where | profile
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Repr

abbrev Value (original : Requirement E V) : Key → Type := fun _ => Profile original
abbrev Object (original : Requirement E V) := LeanPoo.Object.Dataflow.Instance Key (Value original)

def define (name : String) (original : Requirement E V) :
    Except (LeanPoo.Object.Dataflow.Error Key) (Object original) :=
  LeanPoo.Object.Dataflow.define name do
    LeanPoo.Object.Dataflow.Builder.value .profile ⟨original, fun _ _ accepted => accepted⟩

def extend (parent : Object original) (name : String) (extra : Requirement E V) :
    Except (LeanPoo.Object.Dataflow.Error Key) (Object original) :=
  parent.extendWith name do
    LeanPoo.Object.Dataflow.Builder.field .profile
      (.extend (.pure fun _ inherited => inherited.map (fun profile => profile.strengthen extra)))

def contract (original : Requirement E V) : Functional.ObjectProfile.Check Key (Value original) :=
  Functional.ObjectProfile.shape [.profile]

abbrev Session (original : Requirement E V) (object : Object original) :=
  Functional.ObjectProfile.Session (contract original)
    (Functional.ObjectProfile.factory (contract original)) object

def openSession (original : Requirement E V) (object : Object original) :
    Except (List (Issue Key String)) (Session original object) :=
  Functional.ObjectProfile.Session.open (contract original)
    (Functional.ObjectProfile.factory (contract original)) object

theorem selected_child_preserves_original (session : Session original object)
    (profile : Profile original) (read : session.read .profile = some profile)
    (accepted : profile.requirement effect view) :
    object.read .profile = some profile ∧ original effect view :=
  ⟨Functional.ObjectProfile.Access.read_matches session.access .profile profile read,
    profile.refines effect view accepted⟩

variable {parentObject selectedObject : Object original}

/-- Root-index preservation and selected-parent preservation are distinct.
Raw POO overrides may drop an ancestor's additional requirement while retaining
the root. Keep the independently required parent Session and conjoin its actual
projection with the selected Session; no implication solver is invented. -/
structure Composed (requiredParent : Session original parentObject)
    (selected : Session original selectedObject) where
  parentProfile : Profile original
  selectedProfile : Profile original
  parentRead : requiredParent.read .profile = some parentProfile
  selectedRead : selected.read .profile = some selectedProfile

variable {requiredParent : Session original parentObject}
  {selected : Session original selectedObject}

def composeSessions (requiredParent : Session original parentObject)
    (selected : Session original selectedObject) : Option (Composed requiredParent selected) :=
  match parentRead : requiredParent.read .profile, selectedRead : selected.read .profile with
  | some parentProfile, some selectedProfile =>
    some ⟨parentProfile, selectedProfile, parentRead, selectedRead⟩
  | _, _ => none

def Composed.requirement (composition : Composed requiredParent selected) : Requirement E V :=
  strengthen composition.parentProfile.requirement composition.selectedProfile.requirement

theorem composed_preserves_actual_parent_and_original
    (composition : Composed requiredParent selected)
    (accepted : composition.requirement effect view) :
    parentObject.read .profile = some composition.parentProfile ∧
    selectedObject.read .profile = some composition.selectedProfile ∧
    composition.parentProfile.requirement effect view ∧
    composition.selectedProfile.requirement effect view ∧ original effect view :=
  ⟨Functional.ObjectProfile.Access.read_matches requiredParent.access .profile _ composition.parentRead,
    Functional.ObjectProfile.Access.read_matches selected.access .profile _ composition.selectedRead,
    accepted.1, accepted.2, composition.parentProfile.refines _ _ accepted.1⟩

end CedarPooSpec.ZeroTrust.ProfileObject
