import CedarPooSpec.Gateway.Context
import CedarPooSpec.Gateway.Admission
import CedarPooSpec.Gateway.ProfileAdmission
import CedarPooSpec.AuthorizationDeltaOperationalExactProof
import CedarPooSpec.AuthorizationDeltaEvidence

/-! Gateway-scoped composition of the existing authorization/execution Delta.
No alternate solver, Cedar evaluator, Host transaction or delivery ledger. -/
namespace CedarPooSpec.Gateway
open Cedar.Spec CedarPooSpec.PolicyModules

structure DeltaPlan where
  beforeRoot : String
  afterRoot : String
  scope : Scope
  schema : Cedar.Validation.Schema
  revision : Revision
  sourceModules : List PolicyModules.Module

inductive DeltaError where
  | invalidScope
  | environmentChanged
  | compilation (error : PolicyModules.Error)
  deriving Repr

/-- Initial supported profile keeps original semantic/fact/schema scope fixed.
Schema identity must name the actual canonical schema supplied by the Host. -/
def prepareDelta (model : Model) (beforeRoot afterRoot : String)
    (schema : Cedar.Validation.Schema) (beforeScope afterScope : Scope) :
    Except DeltaError DeltaPlan := do
  if !beforeScope.valid || !afterScope.valid then throw .invalidScope
  if beforeScope != afterScope then throw .environmentChanged
  let revision ← (model.compileRevision beforeRoot afterRoot).mapError DeltaError.compilation
  return ⟨beforeRoot, afterRoot, beforeScope, schema, revision, model.modules⟩

/-- Solver-backed report, not a kernel UNSAT certificate or publication permit. -/
def DeltaPlan.analyze (plan : DeltaPlan) :
    IO (Except CedarPooSpec.AuthorizationDelta.ExactOperationalError
      CedarPooSpec.AuthorizationDelta.ExactOperationalImpactReport) :=
  CedarPooSpec.AuthorizationDelta.analyzeExactOperationalImpact plan.revision plan.schema

def DeltaPlan.policyChanges (plan : DeltaPlan) :=
  CedarPooSpec.AuthorizationDelta.Revision.policyChanges plan.revision
def DeltaPlan.provenanceChanges (plan : DeltaPlan) :=
  CedarPooSpec.AuthorizationDelta.Revision.provenanceChanges plan.revision
def DeltaPlan.proofFootprint (plan : DeltaPlan) :=
  CedarPooSpec.AuthorizationDelta.Revision.proofFootprint plan.revision

/-- Content and scope binding at use. Provenance/module authentication remains
separate; equal behavior does not erase changes to source/producer ownership. -/
def DeltaPlan.matchesCurrent (plan : DeltaPlan) (model : Model) (scope : Scope) : Bool :=
  decide (plan.scope = scope ∧ plan.sourceModules = model.modules) &&
  match model.compileRevision plan.beforeRoot plan.afterRoot with
  | .error _ => false
  | .ok current =>
      decide (current.beforePolicies = plan.revision.beforePolicies ∧
        current.afterPolicies = plan.revision.afterPolicies)

/-- Exact upstream query/UNSAT premises, distinct from an executable report.
No constructor converts an empty gain list into this certificate. -/
structure ExactCoverage (schema : Cedar.Validation.Schema) (before after : Policies) : Prop where
  schemaValid : schema.validateWellFormed = .ok ()
  queries : ∀ Γ ∈ schema.environments,
    ∃ typedBefore typedAfter asserts,
      Cedar.SymCC.wellTypedPolicies before Γ = .ok typedBefore ∧
      Cedar.SymCC.wellTypedPolicies after Γ = .ok typedAfter ∧
      CedarPooSpec.AuthorizationDelta.verifyErrorFreeAllowExpansion typedBefore typedAfter
        (Cedar.SymCC.SymEnv.ofTypeEnv Γ) = .ok asserts ∧
      Cedar.SymCC.SymEnv.ofTypeEnv Γ ⊭ asserts

/-- Reuse the actual upstream exact-execution theorem for the plan's policies.
This is pointwise in one validated world; it does not compare changing facts. -/
theorem no_execution_gain_for_validated_input (plan : DeltaPlan)
    (coverage : ExactCoverage plan.schema plan.revision.beforePolicies plan.revision.afterPolicies)
    (env : Cedar.Spec.Env)
    (requestValid : Cedar.Validation.validateRequest plan.schema env.request = .ok ())
    (entitiesValid : Cedar.Validation.validateEntities plan.schema env.entities = .ok ())
    (envWellFormed : env.StronglyWellFormed)
    (beforeWellFormed : env.StronglyWellFormedForPolicies plan.revision.beforePolicies)
    (afterWellFormed : env.StronglyWellFormedForPolicies plan.revision.afterPolicies)
    (allowed : CedarPooSpec.AuthorizationDelta.errorFreeAllow plan.revision.afterPolicies env = true) :
    CedarPooSpec.AuthorizationDelta.errorFreeAllow plan.revision.beforePolicies env = true :=
  CedarPooSpec.AuthorizationDelta.noErrorFreeAllowExpansionForValidatedSchema
    plan.schema plan.revision.beforePolicies plan.revision.afterPolicies
    coverage.schemaValid coverage.queries env requestValid entitiesValid envWellFormed
    beforeWellFormed afterWellFormed allowed

theorem changed_scope_rejects_delta_reuse (plan : DeltaPlan) (model : Model) (scope : Scope)
    (changed : plan.scope ≠ scope) : plan.matchesCurrent model scope = false := by
  simp [DeltaPlan.matchesCurrent, changed]

/-- Compose actual admitted execution with the existing no-expansion theorem.
The explicit policy equality is mandatory: evidence for one revision cannot be
attached to a receipt evaluated under another policy set. Host freshness and
durable consumption are separate obligations. -/
theorem admitted_execution_preserves_delta
    {E S : Type} {projection : E → S → Request} {prepared : Prepared E S projection}
    {model : Model} {effect : E} {state : S} {actualContext : Context}
    {checks : List Assessment} {entities : Entities}
    (receipt : Receipt prepared model effect state actualContext checks entities)
    (plan : DeltaPlan)
    (coverage : ExactCoverage plan.schema plan.revision.beforePolicies plan.revision.afterPolicies)
    (policyBinding : receipt.cedar.policies = plan.revision.afterPolicies)
    (requestValid : Cedar.Validation.validateRequest plan.schema (projection effect state) = .ok ())
    (entitiesValid : Cedar.Validation.validateEntities plan.schema entities = .ok ())
    (envWellFormed : (Env.mk (projection effect state) entities).StronglyWellFormed)
    (beforeWellFormed : (Env.mk (projection effect state) entities).StronglyWellFormedForPolicies
      plan.revision.beforePolicies)
    (afterWellFormed : (Env.mk (projection effect state) entities).StronglyWellFormedForPolicies
      plan.revision.afterPolicies) :
    CedarPooSpec.AuthorizationDelta.errorFreeAllow plan.revision.beforePolicies
      (Env.mk (projection effect state) entities) = true := by
  apply no_execution_gain_for_validated_input plan coverage _ requestValid entitiesValid
    envWellFormed beforeWellFormed afterWellFormed
  have allowed := admitted_actual_request_is_error_free receipt
  simpa [CedarPooSpec.AuthorizationDelta.errorFreeAllow, policyBinding] using allowed

/-- Strong composition interface. Equality authenticates no external source;
the Host still supplies canonical identities, true assessments and current state.
Keeping schema equality explicit lets the theorem reuse actual receipt validation
rather than silently substituting a similarly named schema. -/
structure AdmissionBinding
    {E S : Type} {projection : E → S → Request} {prepared : Prepared E S projection}
    {model : Model} {effect : E} {state : S} {actualContext : Context}
    {checks : List Assessment} {entities : Entities}
    (receipt : Receipt prepared model effect state actualContext checks entities)
    (plan : DeltaPlan) : Prop where
  scopeMatches : plan.scope = actualContext.scope
  schemaMatches : plan.schema = prepared.schema
  sourceMatches : plan.sourceModules = prepared.sourceModules
  rootMatches : plan.afterRoot = prepared.policy.root
  current : plan.matchesCurrent model actualContext.scope = true
  policiesMatch : receipt.cedar.policies = plan.revision.afterPolicies

section BoundLaws
variable {E S : Type} {projection : E → S → Request} {prepared : Prepared E S projection}
  {model : Model} {effect : E} {state : S} {actualContext : Context}
  {checks : List Assessment} {entities : Entities}
  {receipt : Receipt prepared model effect state actualContext checks entities} {plan : DeltaPlan}

theorem bound_delta_preserves_original_scope
    (binding : AdmissionBinding receipt plan) :
    plan.scope = prepared.context.scope :=
  binding.scopeMatches.trans (admitted_original_scope_is_preserved receipt).symm

theorem changed_scope_cannot_bind_admission
    (changed : plan.scope ≠ actualContext.scope) :
    ¬ AdmissionBinding (prepared := prepared) (actualContext := actualContext) receipt plan :=
  fun binding => changed binding.scopeMatches

theorem bound_admitted_execution_preserves_delta
    {E S : Type} {projection : E → S → Request} {prepared : Prepared E S projection}
    {model : Model} {effect : E} {state : S} {actualContext : Context}
    {checks : List Assessment} {entities : Entities}
    (receipt : Receipt prepared model effect state actualContext checks entities)
    (plan : DeltaPlan) (binding : AdmissionBinding receipt plan)
    (coverage : ExactCoverage plan.schema plan.revision.beforePolicies plan.revision.afterPolicies)
    (envWellFormed : (Env.mk (projection effect state) entities).StronglyWellFormed)
    (beforeWellFormed : (Env.mk (projection effect state) entities).StronglyWellFormedForPolicies
      plan.revision.beforePolicies)
    (afterWellFormed : (Env.mk (projection effect state) entities).StronglyWellFormedForPolicies
      plan.revision.afterPolicies) :
    CedarPooSpec.AuthorizationDelta.errorFreeAllow plan.revision.beforePolicies
      (Env.mk (projection effect state) entities) = true :=
  admitted_execution_preserves_delta receipt plan coverage binding.policiesMatch
    (by simpa only [binding.schemaMatches] using receipt.requestValid)
    (by simpa only [binding.schemaMatches] using receipt.entitiesValid)
    envWellFormed beforeWellFormed afterWellFormed

end BoundLaws

/-- Join the actual profile Contract, original scope and exact Delta implication.
Authority authentication and durable CAS remain separate Host obligations. -/
theorem published_execution_preserves_original_and_delta
    {E S : Type} {projection : E → S → Request} {prepared : Prepared E S projection}
    {model : Model} {effect : E} {state : S} {actualContext : Context}
    {checks : List Assessment} {entities : Entities}
    {original : Profile} {object : ProfileObject.Object}
    {publication : ProfileObject.Publication original object}
    (receipt : PublishedReceipt publication prepared model effect state actualContext checks entities)
    (plan : DeltaPlan) (binding : AdmissionBinding receipt.semantic plan)
    (coverage : ExactCoverage plan.schema plan.revision.beforePolicies plan.revision.afterPolicies)
    (envWellFormed : (Env.mk (projection effect state) entities).StronglyWellFormed)
    (beforeWellFormed : (Env.mk (projection effect state) entities).StronglyWellFormedForPolicies
      plan.revision.beforePolicies)
    (afterWellFormed : (Env.mk (projection effect state) entities).StronglyWellFormedForPolicies
      plan.revision.afterPolicies) :
    original.Refines prepared.profile ∧
    prepared.context.scope = publication.context.scope ∧
    CedarPooSpec.AuthorizationDelta.errorFreeAllow plan.revision.beforePolicies
      (Env.mk (projection effect state) entities) = true :=
  ⟨published_profile_refines_authoritative_original receipt, published_scope_cannot_reset receipt,
    bound_admitted_execution_preserves_delta receipt.semantic plan binding coverage envWellFormed
      beforeWellFormed afterWellFormed⟩

end CedarPooSpec.Gateway
