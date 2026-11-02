import CedarPooSpec.ZeroTrust

namespace CedarPooSpec.ZeroTrustObjectTest
open ZeroTrust

def original : Requirement Unit Nat := fun _ value => value ≤ 10
def extra : Requirement Unit Nat := fun _ value => value ≤ 5

def child := do
  let parent ← ProfileObject.define "zero-trust-base" original
  ProfileObject.extend parent "zero-trust-specialization" extra

def readsActualChild : Bool :=
  match child with
  | .error _ => false
  | .ok object =>
    match ProfileObject.openSession original object with
    | .error _ => false
    | .ok session => (session.read .profile).isSome

#guard readsActualChild

-- A raw inherited override can erase an extra parent condition while keeping
-- the original root proof. The root-only shape Contract deliberately admits
-- it; approved parent requirements must be retained at effective invocation.
def rootOnlyProfile : ProfileObject.Profile original :=
  ⟨original, fun _ _ accepted => accepted⟩
def approvedParent : ProfileObject.Profile original := rootOnlyProfile.strengthen extra
def rawOverride := child.bind fun parent => parent.extendWith "root-only-override" do
  LeanPoo.Object.Dataflow.Builder.value .profile rootOnlyProfile

def rootOnlyGateAdmitsOverride : Bool :=
  match rawOverride with
  | .error _ => false
  | .ok object => (ProfileObject.openSession original object).isOk

def composedSessionsRetainBoth : Bool :=
  match child, rawOverride with
  | .ok parent, .ok selected =>
    match ProfileObject.openSession original parent, ProfileObject.openSession original selected with
    | .ok requiredParent, .ok session => (ProfileObject.composeSessions requiredParent session).isSome
    | _, _ => false
  | _, _ => false

#guard rootOnlyGateAdmitsOverride
#guard composedSessionsRetainBoth

theorem raw_override_parent_weakening_counterexample :
    rootOnlyProfile.requirement () 8 ∧ ¬ approvedParent.requirement () 8 := by
  change (8 ≤ 10) ∧ ¬ ((8 ≤ 10) ∧ (8 ≤ 5))
  decide

theorem retained_parent_blocks_that_counterexample :
    ¬ strengthen approvedParent.requirement rootOnlyProfile.requirement () 8 := by
  change ¬ (((8 ≤ 10) ∧ (8 ≤ 5)) ∧ (8 ≤ 10))
  decide

theorem composed_source_reads_and_parent_are_preserved
    {E V : Type} {root : Requirement E V}
    {parentObject selectedObject : ProfileObject.Object root}
    {requiredParent : ProfileObject.Session root parentObject}
    {selected : ProfileObject.Session root selectedObject}
    (effect : E) (view : V)
    (composition : ProfileObject.Composed requiredParent selected)
    (accepted : composition.requirement effect view) :
    parentObject.read .profile = some composition.parentProfile ∧
    selectedObject.read .profile = some composition.selectedProfile ∧
    composition.parentProfile.requirement effect view ∧
    composition.selectedProfile.requirement effect view ∧ root effect view :=
  ProfileObject.composed_preserves_actual_parent_and_original composition accepted

theorem selected_profile_retains_original
    (session : ProfileObject.Session original object)
    (profile : ProfileObject.Profile original)
    (read : session.read .profile = some profile)
    (accepted : profile.requirement () value) : value ≤ 10 :=
  (ProfileObject.selected_child_preserves_original (original := original)
    (effect := ()) (view := value) session profile read accepted).2

theorem weaker_child_is_not_a_refinement :
    ¬ Refines original (fun _ _ => True) := by
  intro refines
  have impossible := refines () 11 True.intro
  simp [original] at impossible

#print axioms selected_profile_retains_original
#print axioms weaker_child_is_not_a_refinement
#print axioms raw_override_parent_weakening_counterexample
#print axioms retained_parent_blocks_that_counterexample
#print axioms composed_source_reads_and_parent_are_preserved
end CedarPooSpec.ZeroTrustObjectTest
