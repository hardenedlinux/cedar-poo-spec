import CedarPooSpec.Authorization.Delta.OperationalExact
import Cedar.Thm.Data.Set
import Cedar.Thm.SymCC.Compiler
import Cedar.Thm.SymCC.Authorizer
import Cedar.Thm.SymCC.Enforcer
import Cedar.Thm.SymCC.WellTyped
import Cedar.Thm.SymCC.Term.Interpret.Factory
import Cedar.Thm.SymCC.Env.Soundness
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.Validation.RequestEntityValidation

/-!
Proof obligations for the composed error-free authorization query. Keep the
concrete diagnostic bridge separate from the solver-backed analyzer.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec Cedar.Data
open Cedar.SymCC
open Cedar.Thm

theorem errorPoliciesEmpty_iff_everyPolicyEvaluates
    (policies : Policies) (request : Request) (entities : Entities) :
    (Cedar.Spec.errorPolicies policies request entities).isEmpty = true ↔
      ∀ policy ∈ policies, Cedar.Spec.hasError policy request entities = false := by
  simp [Cedar.Spec.errorPolicies, Cedar.Spec.errored, List.filterMap_eq_nil_iff]

private theorem hasError_eq_not_isOk (policy : Policy)
    (request : Request) (entities : Entities) :
    Cedar.Spec.hasError policy request entities =
      !(Cedar.Spec.evaluate policy.toExpr request entities).isOk := by
  cases h : Cedar.Spec.evaluate policy.toExpr request entities <;>
    simp [Cedar.Spec.hasError, h, Except.isOk, Except.toBool]

theorem errorPoliciesEmpty_eq_allEvaluationsOk (policies : Policies)
    (request : Request) (entities : Entities) :
    (Cedar.Spec.errorPolicies policies request entities).isEmpty =
      policies.all (fun policy =>
        (Cedar.Spec.evaluate policy.toExpr request entities).isOk) := by
  apply Bool.eq_iff_iff.mpr
  simp [errorPoliciesEmpty_iff_everyPolicyEvaluates,
    hasError_eq_not_isOk, List.all_eq_true]

private theorem isSome_sameResult (result : Cedar.Spec.Result Value)
    (term : Term) (h : result ∼ term) :
    Factory.isSome term = ((result.isOk : Bool) : Term) := by
  change Cedar.SymCC.SameResults result term at h
  cases result <;> cases term <;>
    simp_all [Cedar.SymCC.SameResults, Factory.isSome, Factory.isNone,
      Except.isOk, Except.toBool]

private theorem allEvaluated_sameResults (policies : Policies)
    (terms : List Term) (request : Request) (entities : Entities)
    (h : List.Forall₂ (fun policy term =>
      Cedar.Spec.evaluate policy.toExpr request entities ∼ term) policies terms) :
    allEvaluated terms =
      ((policies.all (fun policy =>
        (Cedar.Spec.evaluate policy.toExpr request entities).isOk)) : Term) := by
  induction h with
  | nil => rfl
  | @cons policy term policies terms hhead htail ih =>
      simp only [allEvaluated, List.all_cons]
      rw [isSome_sameResult _ _ hhead, ih]
      cases (Cedar.Spec.evaluate policy.toExpr request entities).isOk <;>
        cases policies.all (fun policy =>
          (Cedar.Spec.evaluate policy.toExpr request entities).isOk) <;> rfl

private theorem sameResponse_eq_decisionTerm (response : Response)
    (decision : Term) (h : response ∼ decision) :
    decision = ((response.decision == .allow : Bool) : Term) := by
  cases response with
  | mk responseDecision determining erroring =>
      change Cedar.SymCC.SameDecisions responseDecision decision at h
      cases responseDecision <;> cases decision <;>
        simp_all [Cedar.SymCC.SameDecisions]
      case allow.prim prim =>
        cases prim <;> simp_all
        case bool b => cases b <;> simp_all
      case deny.prim prim =>
        cases prim <;> simp_all
        case bool b => cases b <;> simp_all

/-- Pointwise bridge between the composed symbolic execution predicate and
    Cedar's concrete response, assuming the upstream compiler relations for
    the authorization decision and each policy evaluation. -/
theorem symbolicErrorFreeAllow_same (policies : Policies)
    (terms : List Term) (decision : Term) (env : Cedar.Spec.Env)
    (hDecision : Cedar.Spec.isAuthorized env.request env.entities policies ∼ decision)
    (hResults : List.Forall₂ (fun policy term =>
      Cedar.Spec.evaluate policy.toExpr env.request env.entities ∼ term)
        policies terms) :
    symbolicErrorFreeAllow decision terms =
      ((errorFreeAllow policies env : Bool) : Term) := by
  rw [sameResponse_eq_decisionTerm _ _ hDecision]
  unfold symbolicErrorFreeAllow
  rw [allEvaluated_sameResults policies terms env.request env.entities hResults]
  rw [← errorPoliciesEmpty_eq_allEvaluationsOk policies env.request env.entities]
  have errorsExact :
      (Cedar.Spec.isAuthorized env.request env.entities policies).erroringPolicies =
        Cedar.Spec.errorPolicies policies env.request env.entities := by
    simp only [Cedar.Spec.isAuthorized]
    split <;> rfl
  simp only [errorFreeAllow, errorsExact]
  cases hAllow : (Cedar.Spec.isAuthorized env.request env.entities policies).decision ==
      .allow <;>
    cases hErrors : (Cedar.Spec.errorPolicies policies env.request env.entities).isEmpty <;>
      rfl

private theorem allEvaluated_wf_interpret (terms : List Term)
    (εs : Cedar.SymCC.SymEntities) (I : Cedar.SymCC.Interpretation)
    (hWF : ∀ term ∈ terms, term.WellFormed εs)
    (hI : I.WellFormed εs) :
    (allEvaluated terms).WellFormed εs ∧
      (allEvaluated terms).typeOf = .bool ∧
      (allEvaluated terms).interpret I =
        allEvaluated (terms.map (·.interpret I)) := by
  induction terms with
  | nil => simp [allEvaluated, Cedar.Thm.wf_bool]
  | cons term rest ih =>
      have hHead := hWF term (by simp)
      have hTail : ∀ t ∈ rest, t.WellFormed εs := by
        intro t ht
        exact hWF t (by simp [ht])
      obtain ⟨hRestWF, hRestTy, hRestInterp⟩ := ih hTail
      have hSome := Cedar.Thm.wf_isSome hHead
      have hAnd := Cedar.Thm.wf_and hSome.1 hRestWF hSome.2 hRestTy
      refine ⟨hAnd.1, hAnd.2, ?_⟩
      simp only [allEvaluated, List.map_cons]
      rw [Cedar.Thm.interpret_and hI hSome.1 hRestWF hSome.2 hRestTy,
        Cedar.Thm.interpret_isSome hI hHead, hRestInterp]

private theorem allEvaluated_wf (terms : List Term)
    (εs : Cedar.SymCC.SymEntities)
    (hWF : ∀ term ∈ terms, term.WellFormed εs) :
    (allEvaluated terms).WellFormed εs ∧
      (allEvaluated terms).typeOf = .bool := by
  induction terms with
  | nil => simp [allEvaluated, Cedar.Thm.wf_bool]
  | cons term rest ih =>
      have hHead := hWF term (by simp)
      have hTail : ∀ t ∈ rest, t.WellFormed εs := by
        intro t ht
        exact hWF t (by simp [ht])
      have hRest := ih hTail
      have hSome := Cedar.Thm.wf_isSome hHead
      exact Cedar.Thm.wf_and hSome.1 hRest.1 hSome.2 hRest.2

private theorem compiledResultsSame {policies : Policies} {terms : List Term}
    {εnv : SymEnv} {env : Cedar.Spec.Env} {I : Interpretation}
    (hSymbolic : ∀ policy ∈ policies, εnv.WellFormedFor policy.toExpr)
    (hConcrete : ∀ policy ∈ policies, env.WellFormedFor policy.toExpr)
    (hI : I.WellFormed εnv.entities)
    (hEnv : env ∼ εnv.interpret I)
    (hCompiled : policies.mapM (fun policy => compile policy.toExpr εnv) = .ok terms) :
    List.Forall₂ (fun policy term =>
      Cedar.Spec.evaluate policy.toExpr env.request env.entities ∼ term.interpret I)
      policies terms := by
  have pairs := List.mapM_ok_iff_forall₂.mp hCompiled
  induction pairs with
  | nil => exact .nil
  | @cons policy term restPolicies restTerms hHead hTail ih =>
      apply List.Forall₂.cons
      · exact Cedar.Thm.compile_bisimulation
          (hSymbolic policy (by simp)) (hConcrete policy (by simp))
          hI hEnv hHead
      · apply ih
        · intro p hp
          exact hSymbolic p (by simp [hp])
        · intro p hp
          exact hConcrete p (by simp [hp])
        · exact List.mapM_ok_iff_forall₂.mpr hTail

private theorem compiledResultsWF {policies : Policies} {terms : List Term}
    {εnv : SymEnv}
    (hSymbolic : ∀ policy ∈ policies, εnv.WellFormedFor policy.toExpr)
    (hCompiled : policies.mapM (fun policy => compile policy.toExpr εnv) = .ok terms) :
    ∀ term ∈ terms, term.WellFormed εnv.entities := by
  have pairs := List.mapM_ok_iff_forall₂.mp hCompiled
  induction pairs with
  | nil => simp
  | @cons policy term restPolicies restTerms hHead hTail ih =>
      intro current member
      rcases List.mem_cons.mp member with same | tail
      · subst current
        exact (Cedar.Thm.compile_policy_wf
          (hSymbolic policy (by simp)) hHead).1
      · exact ih (by
          intro p hp
          exact hSymbolic p (by simp [hp]))
          (List.mapM_ok_iff_forall₂.mpr hTail) current tail

private theorem forall₂_interpret_right {policies : Policies} {terms : List Term}
    {I : Interpretation} {env : Cedar.Spec.Env}
    (h : List.Forall₂ (fun policy term =>
      Cedar.Spec.evaluate policy.toExpr env.request env.entities ∼ term.interpret I)
      policies terms) :
    List.Forall₂ (fun policy term =>
      Cedar.Spec.evaluate policy.toExpr env.request env.entities ∼ term)
      policies (terms.map (·.interpret I)) := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

/-- The pinned Cedar compiler's bisimulation theorems lift the pointwise
    diagnostic bridge to the actual symbolic query term. -/
theorem symbolicErrorFreeAllow_bisimulation {policies : Policies}
    {terms : List Term} {decision : Term} {εnv : SymEnv}
    {env : Cedar.Spec.Env} {I : Interpretation}
    (hSymbolic : εnv.WellFormedForPolicies policies)
    (hConcrete : env.WellFormedForPolicies policies)
    (hI : I.WellFormed εnv.entities)
    (hEnv : env ∼ εnv.interpret I)
    (hDecision : Cedar.SymCC.isAuthorized policies εnv = .ok decision)
    (hCompiled : policies.mapM (fun policy => compile policy.toExpr εnv) = .ok terms) :
    (symbolicErrorFreeAllow decision terms).interpret I =
      ((errorFreeAllow policies env : Bool) : Term) := by
  have hSymbolicEach : ∀ policy ∈ policies,
      εnv.WellFormedFor policy.toExpr := by
    intro policy member
    exact ⟨hSymbolic.1, hSymbolic.2 policy member⟩
  have hConcreteEach : ∀ policy ∈ policies,
      env.WellFormedFor policy.toExpr := by
    intro policy member
    exact ⟨hConcrete.1, hConcrete.2 policy member⟩
  have hResults := compiledResultsSame hSymbolicEach hConcreteEach
    hI hEnv hCompiled
  have hResults' := forall₂_interpret_right hResults
  have hTermsWF := compiledResultsWF hSymbolicEach hCompiled
  have hAll := allEvaluated_wf_interpret terms εnv.entities I hTermsWF hI
  have hDecisionWF := Cedar.Thm.isAuthorized_wf hSymbolic hDecision
  have hDecisionSame := Cedar.Thm.isAuthorized_bisimulation
    hSymbolic hConcrete hI hEnv hDecision
  unfold symbolicErrorFreeAllow
  rw [Cedar.Thm.interpret_and hI hDecisionWF.1 hAll.1
    hDecisionWF.2 hAll.2.1, hAll.2.2]
  change symbolicErrorFreeAllow (decision.interpret I)
    (terms.map (·.interpret I)) = _
  exact symbolicErrorFreeAllow_same policies _ _ env hDecisionSame hResults'

private theorem symbolicErrorFreeAllow_wf {policies : Policies}
    {terms : List Term} {decision : Term} {εnv : SymEnv}
    (hSymbolic : εnv.WellFormedForPolicies policies)
    (hDecision : Cedar.SymCC.isAuthorized policies εnv = .ok decision)
    (hCompiled : policies.mapM (fun policy => compile policy.toExpr εnv) = .ok terms) :
    (symbolicErrorFreeAllow decision terms).WellFormed εnv.entities ∧
      (symbolicErrorFreeAllow decision terms).typeOf = .bool := by
  have hSymbolicEach : ∀ policy ∈ policies,
      εnv.WellFormedFor policy.toExpr := by
    intro policy member
    exact ⟨hSymbolic.1, hSymbolic.2 policy member⟩
  have hTermsWF := compiledResultsWF hSymbolicEach hCompiled
  have hAll := allEvaluated_wf terms εnv.entities hTermsWF
  have hDecisionWF := Cedar.Thm.isAuthorized_wf hSymbolic hDecision
  exact Cedar.Thm.wf_and hDecisionWF.1 hAll.1 hDecisionWF.2 hAll.2

private theorem verifyErrorFreeAllowExpansion_ok_implies
    {before after : Policies} {εnv : SymEnv} {asserts : Asserts} :
    verifyErrorFreeAllowExpansion before after εnv = .ok asserts →
    ∃ beforeDecision afterDecision beforeResults afterResults,
      Cedar.SymCC.isAuthorized before εnv = .ok beforeDecision ∧
      Cedar.SymCC.isAuthorized after εnv = .ok afterDecision ∧
      before.mapM (fun policy => compile policy.toExpr εnv) = .ok beforeResults ∧
      after.mapM (fun policy => compile policy.toExpr εnv) = .ok afterResults ∧
      asserts = (enforce ((before ++ after).map Policy.toExpr) εnv).elts ++
        [Factory.and
          (symbolicErrorFreeAllow afterDecision afterResults)
          (Factory.not (symbolicErrorFreeAllow beforeDecision beforeResults))] := by
  intro h
  simp only [verifyErrorFreeAllowExpansion] at h
  simp_do_let (Cedar.SymCC.isAuthorized before εnv) at h
  simp_do_let (Cedar.SymCC.isAuthorized after εnv) at h
  simp_do_let (before.mapM fun policy => compile policy.toExpr εnv) at h
  simp_do_let (after.mapM fun policy => compile policy.toExpr εnv) at h
  rename_i beforeDecision hBefore afterDecision hAfter beforeResults hBeforeResults
    afterResults hAfterResults
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨beforeDecision, afterDecision, beforeResults, afterResults,
    rfl, rfl, rfl, rfl, h.symm⟩

/-- An UNSAT answer for the exact query rules out any covered request that
    receives an error-free Allow after the revision but not before it. This
    theorem connects the composed query to upstream Cedar symbolic soundness;
    it does not turn a particular external solver run into a kernel proof. -/
theorem verifyErrorFreeAllowExpansion_is_sound
    {before after : Policies} {εnv : SymEnv} {asserts : Asserts}
    (hSymbolicBefore : εnv.StronglyWellFormedForPolicies before)
    (hSymbolicAfter : εnv.StronglyWellFormedForPolicies after)
    (hQuery : verifyErrorFreeAllowExpansion before after εnv = .ok asserts)
    (hUnsat : εnv ⊭ asserts) :
    ∀ env, env ∈ᵢ εnv →
      env.StronglyWellFormedForPolicies before →
      env.StronglyWellFormedForPolicies after →
      errorFreeAllow after env = true →
      errorFreeAllow before env = true := by
  intro env ⟨I, hI, hEnv⟩ hConcreteBefore hConcreteAfter hAfterAllowed
  obtain ⟨beforeDecision, afterDecision, beforeResults, afterResults,
    hBeforeDecision, hAfterDecision, hBeforeResults, hAfterResults,
    hAsserts⟩ := verifyErrorFreeAllowExpansion_ok_implies hQuery
  have ⟨t, hMember, hNotTrue⟩ :=
    (Cedar.Thm.asserts_unsatisfiable_def.mp hUnsat) I hI
  subst asserts
  have hEnforce := Cedar.Thm.swf_implies_enforce_satisfiedBy hEnv hI
    (Cedar.Thm.swf_εnv_for_policies_iff_swf_for_append.mp
      ⟨hSymbolicBefore, hSymbolicAfter⟩)
    (Cedar.Thm.swf_env_for_policies_iff_swf_for_append.mp
      ⟨hConcreteBefore, hConcreteAfter⟩)
    (by rfl : enforce ((before ++ after).map Policy.toExpr) εnv =
      Set.mk (enforce ((before ++ after).map Policy.toExpr) εnv).elts)
  have hLast := Cedar.Thm.asserts_last_not_true hEnforce hMember hNotTrue
  subst t
  have hSymBefore := Cedar.Thm.swf_εnv_for_policies_implies_wf_for_policies
    hSymbolicBefore
  have hSymAfter := Cedar.Thm.swf_εnv_for_policies_implies_wf_for_policies
    hSymbolicAfter
  have hConBefore := Cedar.Thm.swf_env_for_policies_implies_wf_for_policies
    hConcreteBefore
  have hConAfter := Cedar.Thm.swf_env_for_policies_implies_wf_for_policies
    hConcreteAfter
  have hBeforeWF := symbolicErrorFreeAllow_wf hSymBefore
    hBeforeDecision hBeforeResults
  have hAfterWF := symbolicErrorFreeAllow_wf hSymAfter
    hAfterDecision hAfterResults
  have hNotWF := Cedar.Thm.wf_not hBeforeWF.1 hBeforeWF.2
  rw [Cedar.Thm.interpret_and hI hAfterWF.1 hNotWF.1
    hAfterWF.2 hNotWF.2,
    Cedar.Thm.interpret_not hI hBeforeWF.1,
    symbolicErrorFreeAllow_bisimulation hSymAfter hConAfter hI hEnv
      hAfterDecision hAfterResults,
    symbolicErrorFreeAllow_bisimulation hSymBefore hConBefore hI hEnv
      hBeforeDecision hBeforeResults] at hNotTrue
  rw [hAfterAllowed] at hNotTrue
  cases hBefore : errorFreeAllow before env <;>
    simp_all [Factory.and, Factory.not]

/-- Any concrete covered expansion makes the mathematical query satisfiable.
    The external SMT solver is still responsible for reporting SAT and
    extracting a model; its answer is not itself a Lean proof. -/
theorem verifyErrorFreeAllowExpansion_is_complete_on_witness
    {before after : Policies} {εnv : SymEnv} {asserts : Asserts}
    (hSymbolicBefore : εnv.StronglyWellFormedForPolicies before)
    (hSymbolicAfter : εnv.StronglyWellFormedForPolicies after)
    (hQuery : verifyErrorFreeAllowExpansion before after εnv = .ok asserts)
    (env : Cedar.Spec.Env) (hMember : env ∈ᵢ εnv)
    (hConcreteBefore : env.StronglyWellFormedForPolicies before)
    (hConcreteAfter : env.StronglyWellFormedForPolicies after)
    (hAfterAllowed : errorFreeAllow after env = true)
    (hBeforeDenied : errorFreeAllow before env = false) :
    εnv ⊧ asserts := by
  by_contra hUnsat
  have hBeforeAllowed := verifyErrorFreeAllowExpansion_is_sound
    hSymbolicBefore hSymbolicAfter hQuery hUnsat env hMember
    hConcreteBefore hConcreteAfter hAfterAllowed
  rw [hBeforeDenied] at hBeforeAllowed
  contradiction

/-- Cedar's verified typecheck transformation preserves the full response,
    including erroring policy IDs, on an instance of the type environment. -/
theorem errorFreeAllow_preserved_by_typecheck
    {Γ : Cedar.Validation.TypeEnv} {policies typed : Policies}
    {env : Cedar.Spec.Env}
    (hInstance : Cedar.Thm.InstanceOfWellFormedEnvironment
      env.request env.entities Γ)
    (hTyped : Cedar.SymCC.wellTypedPolicies policies Γ = .ok typed) :
    errorFreeAllow policies env = errorFreeAllow typed env := by
  simp only [errorFreeAllow]
  rw [Cedar.Thm.wellTypedPolicies_preserves_isAuthorized hInstance hTyped]

/-- Cedar's schema validator covers a concrete, strongly well-formed input
    with at least one of the type environments queried by this analyzer. -/
theorem validatedInputCoveredBySchema
    (schema : Cedar.Validation.Schema) (env : Cedar.Spec.Env)
    (hSchema : schema.validateWellFormed = .ok ())
    (hRequest : Cedar.Validation.validateRequest schema env.request = .ok ())
    (hEntities : Cedar.Validation.validateEntities schema env.entities = .ok ())
    (hEnv : env.StronglyWellFormed) :
    ∃ Γ ∈ schema.environments,
      Cedar.Thm.InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
      env ∈ᵢ Cedar.SymCC.SymEnv.ofTypeEnv Γ := by
  obtain ⟨Γ, hΓ, hInstance⟩ :=
    Cedar.Thm.request_and_entities_validate_implies_instance_of_wf_schema
      schema env.request env.entities hSchema hRequest hEntities
  exact ⟨Γ, hΓ, hInstance, Cedar.Thm.ofEnv_soundness hEnv hInstance⟩

/-- Per-environment mathematical UNSAT results lift to all concrete inputs
    admitted by the schema validator. The solver run is still an external
    premise: this theorem consumes proofs of UNSAT, not solver strings. -/
theorem noErrorFreeAllowExpansionForValidatedSchema
    (schema : Cedar.Validation.Schema) (before after : Policies)
    (hSchema : schema.validateWellFormed = .ok ())
    (hQueries : ∀ Γ ∈ schema.environments,
      ∃ typedBefore typedAfter asserts,
        Cedar.SymCC.wellTypedPolicies before Γ = .ok typedBefore ∧
        Cedar.SymCC.wellTypedPolicies after Γ = .ok typedAfter ∧
        verifyErrorFreeAllowExpansion typedBefore typedAfter
          (Cedar.SymCC.SymEnv.ofTypeEnv Γ) = .ok asserts ∧
        Cedar.SymCC.SymEnv.ofTypeEnv Γ ⊭ asserts)
    (env : Cedar.Spec.Env)
    (hRequest : Cedar.Validation.validateRequest schema env.request = .ok ())
    (hEntities : Cedar.Validation.validateEntities schema env.entities = .ok ())
    (hEnv : env.StronglyWellFormed)
    (hBefore : env.StronglyWellFormedForPolicies before)
    (hAfter : env.StronglyWellFormedForPolicies after)
    (hAllowed : errorFreeAllow after env = true) :
    errorFreeAllow before env = true := by
  obtain ⟨Γ, hΓ, hInstance, hMember⟩ :=
    validatedInputCoveredBySchema schema env hSchema hRequest hEntities hEnv
  obtain ⟨typedBefore, typedAfter, asserts, hTypedBefore, hTypedAfter,
    hQuery, hUnsat⟩ := hQueries Γ hΓ
  have hSymbolicBefore := Cedar.Thm.ofEnv_swf_for_policies
    hInstance.wf_env hTypedBefore
  have hSymbolicAfter := Cedar.Thm.ofEnv_swf_for_policies
    hInstance.wf_env hTypedAfter
  have hConcreteBefore := Cedar.Thm.wellTypedPolicies_preserves_StronglyWellFormedForPolicies
    hInstance hTypedBefore hBefore
  have hConcreteAfter := Cedar.Thm.wellTypedPolicies_preserves_StronglyWellFormedForPolicies
    hInstance hTypedAfter hAfter
  have hTypedAllowed : errorFreeAllow typedAfter env = true := by
    rw [← errorFreeAllow_preserved_by_typecheck hInstance hTypedAfter]
    exact hAllowed
  have hTypedBeforeAllowed := verifyErrorFreeAllowExpansion_is_sound
    hSymbolicBefore hSymbolicAfter hQuery hUnsat env hMember
    hConcreteBefore hConcreteAfter hTypedAllowed
  rw [errorFreeAllow_preserved_by_typecheck hInstance hTypedBefore]
  exact hTypedBeforeAllowed

end CedarPooSpec.Authorization.Delta
