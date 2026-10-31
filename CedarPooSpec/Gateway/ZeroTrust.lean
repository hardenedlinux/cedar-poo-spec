import CedarPooSpec.Gateway.Consumption
import CedarPooSpec.Gateway.AuthorizationDelta
import CedarPooSpec.ZeroTrust

/-! Gateway interpretation of the functional Zero Trust framework. Reuse LeanPoo
publication/Contract, Cedar admission, operation/authority ledgers and Delta.
The library performs no IO. Authentication, currentness, atomic durability,
unknown exposure and final mediation are explicit Host refinement obligations.
An equality proof or a solver report is never a transport capability.
Research alignment and the selected per-effect fragment: docs/rfc/0010-zero-trust.org.
This does not mechanize the entire NIST architecture or UCON temporal model. -/
namespace CedarPooSpec.Gateway.ZeroTrust
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
  revoked : View → Prop
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
  notRevoked : ¬ host.revoked actual
  mediated : host.mediated effect actual

variable (proposal : Proposal host publication prepared model effect state actualContext checks entities)

/-- Specialize the functional core through the existing publication-indexed
POO admission contract. Gateway consumes the framework; the core imports none
of these application types. This adapter does not authenticate its Host. -/
def framework : CedarPooSpec.ZeroTrust.Framework E V where
  authenticated := host.authenticated
  authorized := fun requested actual => requested = effect ∧ actual = proposal.before ∧
    host.authoritativeProfile original publication.selected publication.context actual
  currentAtUse := host.currentAtUse
  consumptionCommitted := fun _ actual => host.committed actual proposal.after
  unknownRetained := fun _ actual => host.unknownRetained actual proposal.after
  revoked := fun _ actual => host.revoked actual
  mediated := host.mediated

theorem final_use_satisfies_framework (use : FinalUse proposal) :
    (framework proposal).required effect use.actual :=
  ⟨use.authenticated, ⟨rfl, use.sameView, use.profileAuthority⟩, use.current,
    use.committed, use.unknownRetained, use.notRevoked, use.mediated⟩

/-- POO supplies the original publication and strengthening Contract; the
functional framework supplies conjunction and adaptation. No new object system. -/
def specialize (extra : CedarPooSpec.ZeroTrust.Requirement E V) :
    CedarPooSpec.ZeroTrust.Framework E V :=
  (framework proposal).withRequirement extra

theorem specialization_preserves_core_and_original
    (accepted : (specialize proposal extra).required requested actual) :
    (framework proposal).required requested actual ∧ original.Refines prepared.profile :=
  ⟨CedarPooSpec.ZeroTrust.with_requirement_preserves_framework _ _ _ _ accepted,
    Gateway.published_profile_refines_authoritative_original proposal.receipt⟩

/-- The required parent Session is selected by authoritative publication, not
by the child request. Retain its actual requirement even when raw POO overrides
the child field with a weaker root-only profile. Parent authenticity remains a
Host premise; source-bound projection alone is not authority selection. -/
def fromFrameworkObject
    {parentObject object : CedarPooSpec.ZeroTrust.ProfileObject.Object (framework proposal).required}
    (requiredParent : CedarPooSpec.ZeroTrust.ProfileObject.Session (framework proposal).required parentObject)
    (session : CedarPooSpec.ZeroTrust.ProfileObject.Session (framework proposal).required object) :=
  CedarPooSpec.ZeroTrust.ProfileObject.composeSessions requiredParent session

theorem framework_object_preserves_gateway_contract
    {parentObject object : CedarPooSpec.ZeroTrust.ProfileObject.Object (framework proposal).required}
    (requiredParent : CedarPooSpec.ZeroTrust.ProfileObject.Session (framework proposal).required parentObject)
    (session : CedarPooSpec.ZeroTrust.ProfileObject.Session (framework proposal).required object)
    (composition : CedarPooSpec.ZeroTrust.ProfileObject.Composed requiredParent session)
    (_read : fromFrameworkObject proposal requiredParent session = some composition)
    (accepted : composition.requirement requested actual) :
    parentObject.read .profile = some composition.parentProfile ∧
    object.read .profile = some composition.selectedProfile ∧
    composition.parentProfile.requirement requested actual ∧
    (framework proposal).required requested actual ∧ original.Refines prepared.profile := by
  have projected := CedarPooSpec.ZeroTrust.ProfileObject.composed_preserves_actual_parent_and_original
    composition accepted
  exact ⟨projected.1, projected.2.1, projected.2.2.1, projected.2.2.2.2,
    Gateway.published_profile_refines_authoritative_original proposal.receipt⟩

/-- Explicit recovery refinement evidence: the current authoritative operation
history contains the installed consumption prefix, possibly followed by later
operations. A historical commit label alone cannot construct this witness. -/
structure CommittedPrefix (actual : V) where
  tail : List Admission.OperationId
  installed : (host.operations actual).admitted = proposal.after.operations.admitted ++ tail

/-- Ongoing effects reuse the original consumption, but re-assess current facts.
They do not require equality with the admission pre-state or consume the root
again. The application's assessment must bind the actual effect and current
Cedar world; the framework does not infer it from an earlier Allow. -/
def continuing (assessment : CedarPooSpec.ZeroTrust.Requirement E V) :
    CedarPooSpec.ZeroTrust.Framework E V where
  authenticated := host.authenticated
  authorized := fun requested actual =>
    (host.context actual).scope = prepared.context.scope ∧ assessment requested actual ∧
    host.authoritativeProfile original publication.selected publication.context actual
  currentAtUse := host.currentAtUse
  consumptionCommitted := fun _ actual => host.committed actual proposal.after ∧
    Nonempty (CommittedPrefix proposal actual)
  unknownRetained := fun _ actual => host.unknownRetained actual proposal.after
  revoked := fun _ actual => host.revoked actual
  mediated := host.mediated

theorem committed_prefix_rejects_reconsumption (evidence : CommittedPrefix proposal actual)
    (renewed : Admission.AuthorityLedger E) (renewedId : String) :
    Gateway.consumeAdmission publication proposal.receipt (host.operations actual) renewed renewedId =
      .error .operationAlreadyAdmitted := by
  have originalPrefix := Gateway.consumption_preserves_operation_prefix publication proposal.receipt
    (host.operations proposal.before) (host.authorities proposal.before) proposal.authorityId
    proposal.after proposal.consumption
  have reflexive : (prepared.operationId == prepared.operationId) = true := by
    change (prepared.operationId.value == prepared.operationId.value) = true
    simp
  simp [Gateway.consumeAdmission, Admission.OperationLedger.admit,
    Admission.OperationLedger.check, evidence.installed, originalPrefix,
    List.contains_append, reflexive]

theorem continuing_use_preserves_original_consumption
    (accepted : (continuing proposal assessment).required requested actual)
    (renewed : Admission.AuthorityLedger E) (renewedId : String) :
    (host.context actual).scope = prepared.context.scope ∧
    assessment requested actual ∧ host.unknownRetained actual proposal.after ∧
    Gateway.consumeAdmission publication proposal.receipt (host.operations actual) renewed renewedId =
      .error .operationAlreadyAdmitted := by
  obtain ⟨evidence⟩ := accepted.2.2.2.1.2
  exact ⟨accepted.2.1.1, accepted.2.1.2.1, accepted.2.2.2.2.1,
    committed_prefix_rejects_reconsumption proposal evidence renewed renewedId⟩

/-- Ongoing objects are indexed by the continuing framework, not the initial
same-view admission framework. Compose the same retained POO Sessions and reuse
the existing consumption law; no new root consumption or object engine. -/
theorem continuing_objects_preserve_parent_and_consumption
    {parentObject selectedObject : CedarPooSpec.ZeroTrust.ProfileObject.Object (continuing proposal assessment).required}
    (requiredParent : CedarPooSpec.ZeroTrust.ProfileObject.Session (continuing proposal assessment).required parentObject)
    (selected : CedarPooSpec.ZeroTrust.ProfileObject.Session (continuing proposal assessment).required selectedObject)
    (composition : CedarPooSpec.ZeroTrust.ProfileObject.Composed requiredParent selected)
    (accepted : composition.requirement requested actual)
    (renewed : Admission.AuthorityLedger E) (renewedId : String) :
    composition.parentProfile.requirement requested actual ∧ host.currentAtUse actual ∧
    Nonempty (CommittedPrefix proposal actual) ∧ host.unknownRetained actual proposal.after ∧
    Gateway.consumeAdmission publication proposal.receipt (host.operations actual) renewed renewedId =
      .error .operationAlreadyAdmitted := by
  have projected := CedarPooSpec.ZeroTrust.ProfileObject.composed_preserves_actual_parent_and_original
    composition accepted
  have live := projected.2.2.2.2
  have consumed := continuing_use_preserves_original_consumption proposal live renewed renewedId
  exact ⟨projected.2.2.1, live.2.2.1, live.2.2.2.1.2, consumed.2.2.1, consumed.2.2.2⟩

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
    Authorization.Delta.errorFreeAllow plan.revision.beforePolicies (Env.mk (project effect state) entities) = true := by
  exact ⟨use.current, use.committed,
    Gateway.published_execution_preserves_original_and_delta proposal.receipt plan binding coverage world before after⟩

end CedarPooSpec.Gateway.ZeroTrust
