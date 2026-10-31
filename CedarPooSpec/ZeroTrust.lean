import CedarPooSpec.Gateway.Consumption
import CedarPooSpec.Gateway.AuthorizationDelta

/-! Reusable Zero Trust effect-boundary contract. Reuse the actual LeanPoo
publication/Contract, Cedar admission, operation/authority ledgers and Delta.
The library performs no IO. Authentication, currentness, atomic durability,
unknown exposure and final mediation are explicit Host refinement obligations.
An equality proof or a solver report is never a transport capability.
Research alignment and the selected per-effect fragment: docs/rfc/0010-zero-trust.org.
This does not mechanize the entire NIST architecture or UCON temporal model. -/
namespace CedarPooSpec.ZeroTrust
open Cedar.Spec

/-- View is the application's complete immutable deciding image, not just a
Policy revision. The trusted adapter defines these predicates; a request cannot
choose them or claim currentness by copying labels. No account math is invented. -/
structure Host (Effect View : Type) where
  context : View → Gateway.Context
  operations : View → Admission.OperationLedger
  authorities : View → Admission.AuthorityLedger Effect
  authenticated : View → Prop
  currentAtUse : View → Prop
  authoritativeProfile : Gateway.Profile → Gateway.Profile → Gateway.Context → View → Prop
  committed : View → Gateway.Consumed Effect → Prop
  unknownRetained : View → Gateway.Consumed Effect → Prop
  mediated : Effect → View → Prop

variable {E S V : Type} [BEq E] [LawfulBEq E] {project : E → S → Request}
  {original : Gateway.Profile} {object : Gateway.ProfileObject.Object}
  {publication : Gateway.ProfileObject.Publication original object}
  {prepared : Gateway.Prepared E S project} {model : PolicyModules.Model}
  {effect : E} {state : S} {actualContext : Gateway.Context}
  {checks : List Gateway.Assessment} {entities : Entities}

/-- A pure proposed consumption, indexed by the original object publication.
It carries no send method. Its returned ledgers must be committed at final use. -/
structure Proposal (host : Host E V)
    (publication : Gateway.ProfileObject.Publication original object)
    (prepared : Gateway.Prepared E S project) (model : PolicyModules.Model)
    (effect : E) (state : S) (actualContext : Gateway.Context)
    (checks : List Gateway.Assessment) (entities : Entities) where
  before : V
  receipt : Gateway.PublishedReceipt publication prepared model effect state actualContext checks entities
  contextBound : actualContext = host.context before
  authorityId : String
  after : Gateway.Consumed E
  consumption : Gateway.consumeAdmission publication receipt (host.operations before)
    (host.authorities before) authorityId = .ok after

/-- Higher-order composition over the existing owners. Raw preparation/Receipt
cannot enter this function; no alternate authorization language or evaluator. -/
def propose (host : Host E V) (publication : Gateway.ProfileObject.Publication original object)
    (receipt : Gateway.PublishedReceipt publication prepared model effect state actualContext checks entities)
    (before : V) (contextBound : actualContext = host.context before) (authorityId : String) :
    Except Gateway.ConsumptionError
      (Proposal host publication prepared model effect state actualContext checks entities) :=
  match decision : Gateway.consumeAdmission publication receipt (host.operations before)
      (host.authorities before) authorityId with
  | .error error => .error error
  | .ok after => .ok ⟨before, receipt, contextBound, authorityId, after, decision⟩

variable {host : Host E V}

/-- Host-side final-use proof obligations, deliberately separate from a pure
proposal. The actual linearization must enforce them together before any effect.
Records carry immutable, duplicable evidence, never an affine IO capability.
Fresh native mediation and installation of the returned ledgers remain Host
premises. Object inheritance remains with LeanPoo. -/
structure FinalUse (proposal : Proposal host publication prepared model effect state actualContext checks entities) where
  actual : V
  sameView : actual = proposal.before
  authenticated : host.authenticated actual
  current : host.currentAtUse actual
  profileAuthority : host.authoritativeProfile original publication.selected publication.context actual
  committed : host.committed actual proposal.after
  unknownRetained : host.unknownRetained actual proposal.after
  mediated : host.mediated effect actual

variable (proposal : Proposal host publication prepared model effect state actualContext checks entities)

theorem final_use_preserves_current_context (use : FinalUse proposal) :
    prepared.context = host.context use.actual := by
  rw [use.sameView]
  exact proposal.receipt.semantic.contextMatches.trans proposal.contextBound

theorem final_use_preserves_original_contract (_use : FinalUse proposal) :
    original.Refines prepared.profile :=
  Gateway.published_profile_refines_authoritative_original proposal.receipt

theorem final_use_preserves_original_scope (use : FinalUse proposal) :
    prepared.context.scope = (host.context use.actual).scope :=
  congrArg Gateway.Context.scope (final_use_preserves_current_context proposal use)

theorem final_use_has_error_free_cedar_allow (_use : FinalUse proposal) :
    let response := isAuthorized (project effect state) entities proposal.receipt.semantic.cedar.policies
    (response.decision == .allow && response.erroringPolicies.isEmpty) = true :=
  Gateway.admitted_actual_request_is_error_free proposal.receipt.semantic

theorem returned_ledger_rejects_new_authority (renewed : Admission.AuthorityLedger E) (renewedId : String) :
    Gateway.consumeAdmission publication proposal.receipt proposal.after.operations renewed renewedId =
      .error .operationAlreadyAdmitted :=
  Gateway.renewed_authority_cannot_repeat_consumed_operation publication proposal.receipt
    (host.operations proposal.before) (host.authorities proposal.before) proposal.authorityId
    proposal.after proposal.consumption renewed renewedId

theorem changed_complete_view_cannot_finalize (actual : V) (changed : actual ≠ proposal.before) :
    ¬ ∃ use : FinalUse proposal, use.actual = actual := by
  rintro ⟨use, rfl⟩
  exact changed use.sameView

theorem unknown_or_uncommitted_cannot_finalize (actual : V)
    (absent : ¬ host.committed actual proposal.after) :
    ¬ ∃ use : FinalUse proposal, use.actual = actual := by
  rintro ⟨use, rfl⟩
  exact absent use.committed

theorem zero_trust_final_use (use : FinalUse proposal) :
    host.authenticated use.actual ∧ host.currentAtUse use.actual ∧
    original.Refines prepared.profile ∧
    prepared.context.scope = (host.context use.actual).scope ∧
    host.authoritativeProfile original publication.selected publication.context use.actual ∧
    host.committed use.actual proposal.after ∧ host.unknownRetained use.actual proposal.after ∧
    host.mediated effect use.actual :=
  ⟨use.authenticated, use.current, final_use_preserves_original_contract proposal use,
    final_use_preserves_original_scope proposal use, use.profileAuthority,
    use.committed, use.unknownRetained, use.mediated⟩

/-- Keep actual schema/scope/source/policy binding and upstream exact-query
premises. No empty solver report or changed fact world supplies this proof. -/
theorem final_use_preserves_authorization_delta (use : FinalUse proposal)
    (plan : Gateway.DeltaPlan) (binding : Gateway.AdmissionBinding proposal.receipt.semantic plan)
    (coverage : Gateway.ExactCoverage plan.schema plan.revision.beforePolicies plan.revision.afterPolicies)
    (world : (Env.mk (project effect state) entities).StronglyWellFormed)
    (before : (Env.mk (project effect state) entities).StronglyWellFormedForPolicies plan.revision.beforePolicies)
    (after : (Env.mk (project effect state) entities).StronglyWellFormedForPolicies plan.revision.afterPolicies) :
    host.currentAtUse use.actual ∧ host.committed use.actual proposal.after ∧
    original.Refines prepared.profile ∧ prepared.context.scope = publication.context.scope ∧
    AuthorizationDelta.errorFreeAllow plan.revision.beforePolicies (Env.mk (project effect state) entities) = true := by
  exact ⟨use.current, use.committed,
    Gateway.published_execution_preserves_original_and_delta proposal.receipt plan binding coverage world before after⟩

end CedarPooSpec.ZeroTrust
