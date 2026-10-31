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
end CedarPooSpec.ZeroTrustObjectTest
