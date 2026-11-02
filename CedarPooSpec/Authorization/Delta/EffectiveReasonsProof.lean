import CedarPooSpec.Authorization.Delta.EffectiveReasons
import Cedar.Thm.Authorization

/-!
Concrete meaning of final-reason membership and its reduction to an ordinary
Cedar authorization decision. These proofs are independent of the SMT solver.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec Cedar.Data Cedar.Thm

/-- The executable no-duplicate-ID check supplies Cedar's uniqueness premise. -/
theorem policyIdsUnique_of_nodup (policies : Policies)
    (nodup : (policies.map Policy.id).Nodup) :
    Cedar.Thm.PolicyIdsUnique policies := by
  induction policies with
  | nil => simp [Cedar.Thm.PolicyIdsUnique]
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at nodup
      rcases nodup with ⟨notInTail, tailNodup⟩
      intro first firstMem second secondMem sameId
      simp only [List.mem_cons] at firstMem secondMem
      rcases firstMem with rfl | firstMem
      · rcases secondMem with rfl | secondMem
        · rfl
        · have idInTail : second.id ∈ tail.map Policy.id :=
            List.mem_map.mpr ⟨second, secondMem, rfl⟩
          exact False.elim (notInTail (sameId ▸ idInTail))
      · rcases secondMem with rfl | secondMem
        · have idInTail : first.id ∈ tail.map Policy.id :=
            List.mem_map.mpr ⟨first, firstMem, rfl⟩
          exact False.elim (notInTail (sameId.symm ▸ idInTail))
        · exact ih tailNodup first firstMem second secondMem sameId

/-- Every determining-policy ID comes from the compiled policy list. This
    justifies querying the union of the two revisions' IDs. -/
theorem determiningPolicy_id_from_policies (policies : Policies)
    (env : Cedar.Spec.Env) (id : PolicyID)
    (selected : (Cedar.Spec.isAuthorized env.request env.entities policies).determiningPolicies.contains
      id = true) :
    ∃ policy ∈ policies, policy.id = id := by
  rw [Cedar.Data.Set.contains_prop_bool_equiv] at selected
  rw [Cedar.Thm.determiningPolicies_of] at selected
  unfold Cedar.Spec.satisfiedPolicies at selected
  rw [Cedar.Data.Set.mem_make] at selected
  obtain ⟨policy, member, chosen⟩ := List.mem_filterMap.mp selected
  simp only [Cedar.Spec.satisfiedWithEffect, Bool.and_eq_true,
    beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq] at chosen
  exact ⟨policy, member, chosen.2⟩

/-- A policy ID occurs in Cedar's final reasons exactly when its unique policy
    matches and its effect agrees with the final decision. -/
theorem determiningPolicy_contains_iff (policies : Policies)
    (policy : Policy) (env : Cedar.Spec.Env)
    (unique : Cedar.Thm.PolicyIdsUnique policies)
    (member : policy ∈ policies) :
    (Cedar.Spec.isAuthorized env.request env.entities policies).determiningPolicies.contains
      policy.id =
    (Cedar.Spec.satisfied policy env.request env.entities &&
      (if policy.effect == .permit then
        (Cedar.Spec.isAuthorized env.request env.entities policies).decision == .allow
      else
        (Cedar.Spec.isAuthorized env.request env.entities policies).decision == .deny)) := by
  apply Bool.eq_iff_iff.mpr
  rw [Cedar.Thm.determiningPolicies_of]
  rw [Cedar.Data.Set.contains_prop_bool_equiv]
  unfold Cedar.Spec.satisfiedPolicies
  rw [Cedar.Data.Set.mem_make]
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨other, otherMem, selected⟩
    simp only [Cedar.Spec.satisfiedWithEffect, Bool.and_eq_true,
      beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq] at selected
    have same : other = policy := unique other otherMem policy member selected.2
    subst same
    rcases selected with ⟨⟨effect, matched⟩, _⟩
    cases decision : (Cedar.Spec.isAuthorized env.request env.entities policies).decision <;>
      cases kind : other.effect <;> simp_all
  · intro selected
    refine ⟨policy, member, ?_⟩
    simp only [Cedar.Spec.satisfiedWithEffect, Bool.and_eq_true,
      beq_iff_eq, Option.ite_none_right_eq_some]
    cases decision : (Cedar.Spec.isAuthorized env.request env.entities policies).decision <;>
      cases kind : policy.effect <;> simp_all

/-- A permit whose matches are covered by a matching forbid cannot be a
    determining policy in Cedar's final response. -/
theorem dominatedPermit_not_determining (policies : Policies)
    (permit forbid : Policy) (env : Cedar.Spec.Env)
    (unique : Cedar.Thm.PolicyIdsUnique policies)
    (permitMem : permit ∈ policies) (forbidMem : forbid ∈ policies)
    (permitEffect : permit.effect = .permit)
    (forbidEffect : forbid.effect = .forbid)
    (covered : Cedar.Spec.satisfied permit env.request env.entities = true →
      Cedar.Spec.satisfied forbid env.request env.entities = true) :
    (Cedar.Spec.isAuthorized env.request env.entities policies).determiningPolicies.contains
      permit.id = false := by
  by_cases matched : Cedar.Spec.satisfied permit env.request env.entities = true
  · have explicitlyForbidden : Cedar.Thm.IsExplicitlyForbidden
        env.request env.entities policies :=
      ⟨forbid, forbidMem, forbidEffect, covered matched⟩
    have denied := Cedar.Thm.forbid_trumps_permit env.request env.entities policies
      explicitlyForbidden
    rw [determiningPolicy_contains_iff policies permit env unique permitMem,
      permitEffect, matched, denied]
    rfl
  · rw [determiningPolicy_contains_iff policies permit env unique permitMem]
    cases satisfied : Cedar.Spec.satisfied permit env.request env.entities <;>
      simp_all

private theorem surrogate_forbids (policies : Policies) (policy : Policy)
    (request : Request) (entities : Entities) (effect : policy.effect = .permit) :
    IsExplicitlyForbidden request entities
      (policies.filter (·.effect == .forbid) ++ [policy]) ↔
    IsExplicitlyForbidden request entities policies := by
  simp [IsExplicitlyForbidden, HasSatisfiedEffect, effect, and_assoc]

private theorem surrogate_permits (policies : Policies) (policy : Policy)
    (request : Request) (entities : Entities) (effect : policy.effect = .permit) :
    IsExplicitlyPermitted request entities
      (policies.filter (·.effect == .forbid) ++ [policy]) ↔
    satisfied policy request entities = true := by
  simp [IsExplicitlyPermitted, HasSatisfiedEffect, effect, and_assoc]
  intro other member forbid permit matched
  simp [forbid] at permit

private theorem permit_surrogate (policies : Policies) (policy : Policy)
    (request : Request) (entities : Entities) (effect : policy.effect = .permit)
    (member : policy ∈ policies) :
    (isAuthorized request entities
      (policies.filter (·.effect == .forbid) ++ [policy])).decision = .allow ↔
    satisfied policy request entities = true ∧
      (isAuthorized request entities policies).decision = .allow := by
  rw [← allowed_iff_explicitly_permitted_and_not_denied,
    surrogate_permits policies policy request entities effect,
    surrogate_forbids policies policy request entities effect]
  rw [← allowed_iff_explicitly_permitted_and_not_denied]
  constructor
  · rintro ⟨matched, noForbid⟩
    exact ⟨matched, ⟨⟨policy, member, effect, matched⟩, noForbid⟩⟩
  · rintro ⟨matched, _, noForbid⟩
    exact ⟨matched, noForbid⟩

private theorem forbid_surrogate (policy : Policy) (request : Request)
    (entities : Entities) :
    (isAuthorized request entities [{policy with effect := .permit}]).decision = .allow ↔
    satisfied policy request entities = true := by
  rw [← allowed_iff_explicitly_permitted_and_not_denied]
  simp [IsExplicitlyPermitted, IsExplicitlyForbidden, HasSatisfiedEffect,
    satisfied, Policy.toExpr]
  rfl

/-- Under unique policy IDs, membership in the original final reason set is
    exactly the Allow decision of the analysis-only policyset. The latter can
    be compared by Cedar's verified authorization-equivalence query. -/
theorem reasonPolicyset_allows_iff_determining (policies : Policies)
    (id : PolicyID) (env : Cedar.Spec.Env)
    (unique : Cedar.Thm.PolicyIdsUnique policies) :
    ((isAuthorized env.request env.entities (reasonPolicyset policies id)).decision == .allow) =
    (isAuthorized env.request env.entities policies).determiningPolicies.contains id := by
  apply Bool.eq_iff_iff.mpr
  unfold reasonPolicyset
  split
  · rename_i absent
    have noId : ∀ policy ∈ policies, policy.id ≠ id := by
      intro policy member sameId
      have missing := (List.find?_eq_none.mp absent) policy member
      simp [sameId] at missing
    constructor
    · intro allowed
      simp [isAuthorized, satisfiedPolicies, satisfiedWithEffect,
        Cedar.Data.Set.make, Cedar.Data.Set.isEmpty] at allowed
    · intro selected
      have found : ∃ policy ∈ policies, policy.id = id :=
        determiningPolicy_id_from_policies policies env id (by simpa using selected)
      obtain ⟨policy, member, sameId⟩ := found
      exact False.elim (noId policy member sameId)
  · rename_i policy found
    have member : policy ∈ policies := List.mem_of_find?_eq_some found
    have sameId : policy.id = id := by
      have selected := List.find?_some found
      simpa using selected
    rw [← sameId]
    split
    · rename_i permit
      have effect : policy.effect = .permit := by simpa using permit
      rw [determiningPolicy_contains_iff policies policy env unique member]
      simpa [effect] using
        (permit_surrogate policies policy env.request env.entities effect member)
    · rename_i notPermit
      have effect : policy.effect = .forbid := by
        cases actual : policy.effect <;> simp_all
      rw [determiningPolicy_contains_iff policies policy env unique member]
      have denied : satisfied policy env.request env.entities = true →
          (isAuthorized env.request env.entities policies).decision = .deny := by
        intro matched
        exact forbid_trumps_permit env.request env.entities policies
          ⟨policy, member, effect, matched⟩
      constructor
      · intro allowed
        have matched := (forbid_surrogate policy env.request env.entities).mp
          (by simpa using allowed)
        simp [effect, matched, denied matched]
      · intro selected
        have matchedAndDenied : satisfied policy env.request env.entities = true ∧
            (isAuthorized env.request env.entities policies).decision = .deny := by
          simpa [effect] using selected
        simpa using (forbid_surrogate policy env.request env.entities).mpr
          matchedAndDenied.1

end CedarPooSpec.Authorization.Delta
