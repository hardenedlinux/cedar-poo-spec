import CedarPooSpec.ZeroTrust.Model

namespace CedarPooSpec.ZeroTrust

def strengthen (base extra : Requirement E V) : Requirement E V :=
  fun effect view => base effect view ∧ extra effect view

def adapt (requirement : Requirement E V) (effect : E' → E) (view : V' → V) :
    Requirement E' V' := fun e v => requirement (effect e) (view v)

def Refines (base selected : Requirement E V) : Prop :=
  ∀ effect view, selected effect view → base effect view

theorem strengthen_refines (base extra : Requirement E V) :
    Refines base (strengthen base extra) := fun _ _ accepted => accepted.1

theorem refinement_trans (ab : Refines a b) (bc : Refines b c) : Refines a c :=
  fun e v accepted => ab e v (bc e v accepted)

theorem adapt_preserves_refinement {base selected : Requirement E V}
    (refines : Refines base selected)
    (effect : E' → E) (view : V' → V) :
    Refines (adapt base effect view) (adapt selected effect view) :=
  fun e v accepted => refines (effect e) (view v) accepted

def Framework.required (framework : Framework E V) : Requirement E V :=
  fun effect view => framework.authenticated view ∧ framework.authorized effect view ∧
    framework.currentAtUse view ∧ framework.consumptionCommitted effect view ∧
    framework.unknownRetained effect view ∧ ¬ framework.revoked effect view ∧
    framework.mediated effect view

/-- Purely strengthens the supplied authorization meaning; it cannot replace
identity, persistence, revocation or mediation with a weaker child predicate. -/
def Framework.withRequirement (framework : Framework E V) (extra : Requirement E V) :
    Framework E V :=
  { framework with authorized := strengthen framework.authorized extra }

theorem with_requirement_preserves_framework (framework : Framework E V)
    (extra : Requirement E V) :
    Refines framework.required (framework.withRequirement extra).required := by
  intro effect view accepted
  exact ⟨accepted.1, accepted.2.1.1, accepted.2.2⟩


end CedarPooSpec.ZeroTrust
