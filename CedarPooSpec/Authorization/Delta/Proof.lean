import CedarPooSpec.Revision
import Cedar.Thm.WellTypedVerification

/-!
The logical boundary of an authorization-delta query. Solver output is not
converted into `εnv ⊭ asserts` by this module; that premise must be proved in
Lean before the conclusion can be used as a theorem.
-/

namespace CedarPooSpec.PolicyModules

open Cedar.Spec Cedar.Validation Cedar.SymCC Cedar.Thm

/-- Transport Cedar's verified implication result to the original policy sets
    produced by one POO revision. The query runs on typechecked policies;
    Cedar's theorem transfers the result back to those original policies. -/
theorem Revision.noExpansionOfUnsat (revision : Revision) (Γ : TypeEnv)
    (typedAfter typedBefore : Policies) (asserts : Asserts)
    (hwf : Γ.WellFormed)
    (hafter : wellTypedPolicies revision.afterPolicies Γ = .ok typedAfter)
    (hbefore : wellTypedPolicies revision.beforePolicies Γ = .ok typedBefore)
    (hquery : verifyImplies typedAfter typedBefore (SymEnv.ofTypeEnv Γ) = .ok asserts)
    (hunsat : SymEnv.ofTypeEnv Γ ⊭ asserts)
    (env : Env)
    (hinstance : InstanceOfWellFormedEnvironment env.request env.entities Γ)
    (hstrongAfter : env.StronglyWellFormedForPolicies typedAfter)
    (hstrongBefore : env.StronglyWellFormedForPolicies typedBefore) :
    ifFirstAllowsSoDoesSecond
      (Cedar.Spec.isAuthorized env.request env.entities revision.afterPolicies)
      (Cedar.Spec.isAuthorized env.request env.entities revision.beforePolicies) := by
  obtain ⟨generated, hgenerated, hsound⟩ :=
    verifyImplies_is_ok_and_sound hwf hafter hbefore
  have heq : generated = asserts := by
    rw [hquery] at hgenerated
    cases hgenerated
    rfl
  subst generated
  exact hsound hunsat env hinstance hstrongAfter hstrongBefore

end CedarPooSpec.PolicyModules
