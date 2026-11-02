import CedarPooSpec.Authorization.Delta.OperationalExactProof
import Examples.Governance.TicketSharing

/-!
Direct Cedar evaluation proof for the linked ticket-sharing policy revision.
Two permit conditions add `deviceTrusted`; the third policy is reused. The
proof covers both the decision and erroring-policy set for every Cedar Env.
Its dependency audit checks that it uses only Lean's standard axioms.
-/

namespace CedarPooSpec.AuthorizationDeltaDirect

open Cedar.Spec Cedar.Thm CedarPooSpec.TicketSharingExample

private theorem tightened_satisfied (p : Policy) (e guard : Expr)
    (req : Request) (entities : Entities)
    (h : satisfied { p with condition := [{ kind := .when, body := .and e guard }] } req entities = true) :
    satisfied { p with condition := [{ kind := .when, body := e }] } req entities = true := by
  have he : evaluate (Expr.and e guard) req entities = .ok true := by
    have h' := of_decide_eq_true h
    simp only [Policy.toExpr, Conditions.toExpr, Condition.toExpr] at h'
    exact and_true_implies_right_true
      (and_true_implies_right_true
        (and_true_implies_right_true h'))
  have he' := and_true_implies_left_true he
  have h' := of_decide_eq_true h
  simp only [Policy.toExpr, Conditions.toExpr, Condition.toExpr] at h'
  have hp := and_true_implies_left_true h'
  have ha := and_true_implies_left_true (and_true_implies_right_true h')
  have hr := and_true_implies_left_true
    (and_true_implies_right_true (and_true_implies_right_true h'))
  apply decide_eq_true
  simp only [Policy.toExpr, Conditions.toExpr, Condition.toExpr]
  exact and_bool_operands_is_boolean_and hp
    (and_bool_operands_is_boolean_and ha
      (and_bool_operands_is_boolean_and hr he'))

private def oldA : Policy := publishedPolicies[0]!
private def oldB : Policy := publishedPolicies[1]!
private def sharedV : Policy := publishedPolicies[2]!

private theorem before_shape : publishedPolicies = [oldA, oldB, sharedV] := by decide
private theorem after_shape : posturePolicies =
    [{oldA with condition := [{ kind := .when, body := .and openTicket trustedDevice }]},
     {oldB with condition := [{ kind := .when, body := .and openTicket trustedDevice }]},
     sharedV] := by decide
private theorem oldA_condition : oldA.condition = [{ kind := .when, body := openTicket }] := by decide
private theorem oldB_condition : oldB.condition = [{ kind := .when, body := openTicket }] := by decide

private theorem all_permit : oldA.effect = .permit ∧ oldB.effect = .permit ∧ sharedV.effect = .permit := by decide

private theorem decision_no_gain (req : Request) (entities : Entities)
    (h : (isAuthorized req entities posturePolicies).decision = .allow) :
    (isAuthorized req entities publishedPolicies).decision = .allow := by
  have hPermit := Cedar.Thm.allowed_only_if_explicitly_permitted req entities posturePolicies h
  have hBeforePermit : Cedar.Thm.IsExplicitlyPermitted req entities publishedPolicies := by
    obtain ⟨p, hp, heff, hs⟩ := hPermit
    rw [after_shape] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · refine ⟨oldA, ?_, all_permit.1, ?_⟩
      · rw [before_shape]; simp
      · have hmatch := tightened_satisfied oldA openTicket trustedDevice req entities hs
        simpa only [← oldA_condition] using hmatch
    · refine ⟨oldB, ?_, all_permit.2.1, ?_⟩
      · rw [before_shape]; simp
      · have hmatch := tightened_satisfied oldB openTicket trustedDevice req entities hs
        simpa only [← oldB_condition] using hmatch
    · exact ⟨sharedV, by rw [before_shape]; simp, all_permit.2.2, hs⟩
  have hNoForbid : ¬ Cedar.Thm.IsExplicitlyForbidden req entities publishedPolicies := by
    intro hf
    obtain ⟨p, hp, heffect, _⟩ := hf
    rw [before_shape] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [all_permit] at heffect
  exact (Cedar.Thm.allowed_iff_explicitly_permitted_and_not_denied req entities publishedPolicies).mp
    ⟨hBeforePermit, hNoForbid⟩


private theorem and_ok_left_bool (e guard : Expr) (req : Request) (entities : Entities)
    (h : ∃ b : Bool, evaluate (.and e guard) req entities = .ok b) :
    ∃ b : Bool, evaluate e req entities = .ok b := by
  obtain ⟨b, hb⟩ := h
  cases he : evaluate e req entities with
  | error err => simp [evaluate, he, Result.as] at hb
  | ok v =>
    cases v with
    | prim p =>
      cases p with
      | bool be => exact ⟨be, rfl⟩
      | int i => simp [evaluate, he, Result.as, Coe.coe, Value.asBool] at hb
      | string s => simp [evaluate, he, Result.as, Coe.coe, Value.asBool] at hb
      | entityUID uid => simp [evaluate, he, Result.as, Coe.coe, Value.asBool] at hb
    | set s => simp [evaluate, he, Result.as, Coe.coe, Value.asBool] at hb
    | record r => simp [evaluate, he, Result.as, Coe.coe, Value.asBool] at hb
    | ext x => simp [evaluate, he, Result.as, Coe.coe, Value.asBool] at hb

private theorem and_right_replace_ok (x y z : Expr) (req : Request) (entities : Entities)
    (hyz : (∃ b : Bool, evaluate y req entities = .ok b) →
      ∃ b : Bool, evaluate z req entities = .ok b)
    (h : ∃ b : Bool, evaluate (.and x y) req entities = .ok b) :
    ∃ b : Bool, evaluate (.and x z) req entities = .ok b := by
  obtain ⟨b, hb⟩ := h
  cases hx : evaluate x req entities with
  | error err => simp [evaluate, hx, Result.as] at hb
  | ok v =>
    cases v with
    | prim p =>
      cases p with
      | bool bx =>
        cases bx with
        | false =>
          exact ⟨false, by simp [evaluate, hx, Result.as, Coe.coe, Value.asBool]⟩
        | true =>
          have hy : ∃ byy : Bool, evaluate y req entities = .ok byy := by
            -- The true left operand forces evaluation of the right operand.
            simp [evaluate, hx, Result.as, Coe.coe, Value.asBool] at hb
            cases hy0 : evaluate y req entities with
            | error err => simp [hy0] at hb
            | ok vy =>
              cases vy with
              | prim py =>
                cases py with
                | bool byy => exact ⟨byy, rfl⟩
                | int i => simp [hy0] at hb
                | string s => simp [hy0] at hb
                | entityUID uid => simp [hy0] at hb
              | set s => simp [hy0] at hb
              | record r => simp [hy0] at hb
              | ext ex => simp [hy0] at hb
          obtain ⟨bz, hz⟩ := hyz hy
          exact ⟨bz, by simp [evaluate, hx, hz, Result.as, Coe.coe, Value.asBool]⟩
      | int i => simp [evaluate, hx, Result.as, Coe.coe, Value.asBool] at hb
      | string s => simp [evaluate, hx, Result.as, Coe.coe, Value.asBool] at hb
      | entityUID uid => simp [evaluate, hx, Result.as, Coe.coe, Value.asBool] at hb
    | set s => simp [evaluate, hx, Result.as, Coe.coe, Value.asBool] at hb
    | record r => simp [evaluate, hx, Result.as, Coe.coe, Value.asBool] at hb
    | ext ex => simp [evaluate, hx, Result.as, Coe.coe, Value.asBool] at hb

private theorem tightened_no_error (p : Policy) (e guard : Expr)
    (req : Request) (entities : Entities)
    (h : hasError { p with condition := [{ kind := .when, body := .and e guard }] }
      req entities = false) :
    hasError { p with condition := [{ kind := .when, body := e }] }
      req entities = false := by
  let newer : Policy := { p with condition := [{ kind := .when, body := .and e guard }] }
  let older : Policy := { p with condition := [{ kind := .when, body := e }] }
  have hbool : ∃ b : Bool, evaluate newer.toExpr req entities = .ok b := by
    have ht := policy_produces_bool_or_error newer req entities
    cases he : evaluate newer.toExpr req entities with
    | error err => simp [hasError, newer, he] at h
    | ok v =>
      cases v with
      | prim prim =>
        cases prim with
        | bool b => exact ⟨b, rfl⟩
        | int i => simp [he] at ht
        | string s => simp [he] at ht
        | entityUID uid => simp [he] at ht
      | set s => simp [he] at ht
      | record r => simp [he] at ht
      | ext ex => simp [he] at ht
  have hOld : ∃ b : Bool, evaluate older.toExpr req entities = .ok b := by
    simp only [newer, older, Policy.toExpr, Conditions.toExpr, Condition.toExpr] at hbool ⊢
    apply and_right_replace_ok _ _ _ req entities
    · intro hinner
      apply and_right_replace_ok _ _ _ req entities
      · intro hinner2
        apply and_right_replace_ok _ _ _ req entities
        · exact and_ok_left_bool e guard req entities
        · exact hinner2
      · exact hinner
    · exact hbool
  obtain ⟨b, hb⟩ := hOld
  simp [hasError, older, hb]
/-- A successful error-free Allow in the revised linked policies was already
    an error-free Allow in the earlier linked policies, for every Cedar Env. -/
theorem noErrorFreeAllowGain (env : Cedar.Spec.Env)
    (h : CedarPooSpec.Authorization.Delta.errorFreeAllow posturePolicies env = true) :
    CedarPooSpec.Authorization.Delta.errorFreeAllow publishedPolicies env = true := by
  have errorsExact (ps : Policies) :
      (isAuthorized env.request env.entities ps).erroringPolicies =
        errorPolicies ps env.request env.entities := by
    simp only [isAuthorized]
    split <;> rfl
  have hAfterParts :
      (isAuthorized env.request env.entities posturePolicies).decision = .allow ∧
      (errorPolicies posturePolicies env.request env.entities).isEmpty = true := by
    simpa only [CedarPooSpec.Authorization.Delta.errorFreeAllow,
      errorsExact, Bool.and_eq_true, beq_iff_eq] using h
  have hBeforeDecision := decision_no_gain env.request env.entities hAfterParts.1
  have hAfterEval : ∀ p ∈ posturePolicies, hasError p env.request env.entities = false :=
    (CedarPooSpec.Authorization.Delta.errorPoliciesEmpty_iff_everyPolicyEvaluates
      posturePolicies env.request env.entities).mp hAfterParts.2
  have hBeforeEval : ∀ p ∈ publishedPolicies, hasError p env.request env.entities = false := by
    intro p hp
    rw [before_shape] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · have hn := hAfterEval
        {oldA with condition := [{ kind := .when, body := .and openTicket trustedDevice }]}
        (by rw [after_shape]; simp)
      have ho := tightened_no_error oldA openTicket trustedDevice env.request env.entities hn
      simpa only [← oldA_condition] using ho
    · have hn := hAfterEval
        {oldB with condition := [{ kind := .when, body := .and openTicket trustedDevice }]}
        (by rw [after_shape]; simp)
      have ho := tightened_no_error oldB openTicket trustedDevice env.request env.entities hn
      simpa only [← oldB_condition] using ho
    · exact hAfterEval sharedV (by rw [after_shape]; simp)
  have hBeforeErrors :=
    (CedarPooSpec.Authorization.Delta.errorPoliciesEmpty_iff_everyPolicyEvaluates
      publishedPolicies env.request env.entities).mpr hBeforeEval
  simpa only [CedarPooSpec.Authorization.Delta.errorFreeAllow,
    errorsExact, Bool.and_eq_true, beq_iff_eq] using
    (show (isAuthorized env.request env.entities publishedPolicies).decision = .allow ∧
      (errorPolicies publishedPolicies env.request env.entities).isEmpty = true from
      ⟨hBeforeDecision, hBeforeErrors⟩)

/-- The C4 revision compiles to these exact linked policies. This wrapper
    inherits the fixture's model-construction certificates. -/
theorem noErrorFreeAllowGainForRevision (env : Cedar.Spec.Env)
    (h : CedarPooSpec.Authorization.Delta.errorFreeAllow
      policyRevision.afterPolicies env = true) :
    CedarPooSpec.Authorization.Delta.errorFreeAllow
      policyRevision.beforePolicies env = true := by
  obtain ⟨hBefore, hAfter⟩ := policyRevisionBodies
  rw [hAfter] at h
  rw [hBefore]
  exact noErrorFreeAllowGain env h

end CedarPooSpec.AuthorizationDeltaDirect
