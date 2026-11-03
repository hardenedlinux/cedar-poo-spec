import CedarPooSpec.Gateway.ReviewedEffect

/-! Current-use safety after source renewal, revocation and mediator recovery.
The Host must supply the actual current image and realize its atomic writers.
Historical publication approval is not a fresh-world Cedar receipt. -/
namespace CedarPooSpec.Gateway.Lifecycle
open EffectProtocol LeanPoo.Functional.DeclarativeMetadata

structure State where
  current : Current
  generation : Nat := 0
  owner : Nat := 0
  factGeneration : Nat := 7
  spent : Bool := false
  sourcesCurrent : Bool := true
  publicationUnknown : Bool := false
  cedarAllowed : Bool

structure Handle where
  generation : Nat
  owner : Nat
  deriving DecidableEq

def freshHandle (state : State) : Handle := ⟨state.generation, state.owner⟩
def allowed (state : State) (handle : Handle) (envelope : Envelope) : Bool :=
  decide (handle = freshHandle state) && state.sourcesCurrent && !state.spent && !state.publicationUnknown &&
    accepts state.current envelope state.cedarAllowed

def use (state : State) (handle : Handle) (envelope : Envelope) : Outcome :=
  Outcome.resolve (allowed state handle envelope) true false

/-- This is the actual POO Contract for the current-use result, not an approval flag. -/
def contract : Contract Unit (State × Handle × Envelope) Outcome where
  input := ⟨"current-use", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"current-outcome", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => result = use input.1 input.2.1 input.2.2
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : State × Handle × Envelope) : Except String (Outcome × Unit) :=
  .ok (use input.1 input.2.1 input.2.2, ())

def invoke (state : State) (handle : Handle) (envelope : Envelope) :=
  contract.invoke prepare (state,handle,envelope)


/-- Source preparation yields exact field evidence under the original inventory.
Signature verification is the independently configured Host interpretation. -/
def sourceContract (authority : CedarPooSpec.ZeroTrust.FactAuthority String String)
    (required : List String)
    (verified : CedarPooSpec.ZeroTrust.FactStatement String String → Bool) :
    Contract Unit (List (CedarPooSpec.ZeroTrust.FactStatement String String))
      (List (CedarPooSpec.ZeroTrust.FactBinding String String)) where
  input := ⟨"source-statements", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"verified-fields", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => result = input.flatMap (·.facts) ∧
    authority.acceptsStatements required input verified = true
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareStatements (authority : CedarPooSpec.ZeroTrust.FactAuthority String String)
    (required : List String)
    (verified : CedarPooSpec.ZeroTrust.FactStatement String String → Bool)
    (statements : List (CedarPooSpec.ZeroTrust.FactStatement String String)) :
    Except String (List (CedarPooSpec.ZeroTrust.FactBinding String String) × Unit) :=
  if authority.acceptsStatements required statements verified then
    .ok (statements.flatMap (·.facts), ()) else .error "source statement admission refused"

theorem source_invocation_preserves_field_admission
    (authority : CedarPooSpec.ZeroTrust.FactAuthority String String)
    (required : List String)
    (verified : CedarPooSpec.ZeroTrust.FactStatement String String → Bool)
    (statements : List (CedarPooSpec.ZeroTrust.FactStatement String String))
    (receipt : Invocation (sourceContract authority required verified)
      (prepareStatements authority required verified) statements) :
    authority.acceptsAll required receipt.result = true := by
  have bound := receipt.logic
  simp only [sourceContract, Formula.Holds] at bound
  rw [bound.1]
  exact CedarPooSpec.ZeroTrust.accepted_statements_preserve_field_admission
    authority required statements verified bound.2

def revoke (state : State) : State :=
  { state with current := { state.current with revoked := true }, generation := state.generation + 1 }

/-- Renewal uses newly interpreted authority and a newly evaluated SDK world;
no grant, revocation flag, epoch or unresolved effect is reset. -/
def renew (state : State) (authority : CedarPooSpec.ZeroTrust.FactAuthority String String)
    (required : List String) (world : String) (cedarAllowed : Bool) : State :=
  { state with
    current := { state.current with
      authority := { authority with now := state.current.authority.now }
      required := required
      world := world }
    generation := state.generation + 1
    factGeneration := state.factGeneration + 1
    sourcesCurrent := true
    cedarAllowed := cedarAllowed }

/-- An independent complete outcome may resolve uncertainty; the original burn
and all current authorization inputs survive. The mediator owner is replaced. -/
def recover (state : State) (committed complete : Bool) : State :=
  let spent := state.spent || committed
  { state with
    spent := spent
    generation := state.generation + 1
    owner := state.owner + 1
    current := { state.current with unknown :=
      if spent || state.current.unknown then !(committed && complete) else state.current.unknown } }

/-- A live publication strengthens the existing exact-successor Contract using
current source evidence and its pinned publication world. -/
def publicationGuard (state : State) (pinned : String) (envelope : Envelope) : Bool :=
  decide (state.current.world = pinned) &&
    (currentEvidence state.current envelope && state.current.enforcing && state.current.mapped &&
      !state.current.revoked && state.current.registered && !state.current.unknown &&
      !state.publicationUnknown && state.sourcesCurrent && state.current.consumed && !state.spent)

def publicationContract (reviewed : Authorization.Delta.ReviewedInteraction)
    (model : PolicyModules.Model) (schema : Cedar.Validation.Schema)
    (before : Authorization.Delta.ReleaseState) (state : State) (pinned : String) (envelope : Envelope) :=
  let original := ReviewedEffect.contract reviewed model schema before
  original.withMeaning
    (fun atom approved result => original.meaning atom approved result ∧ before.epoch = state.current.review.epoch ∧
      publicationGuard state pinned envelope = true)
    (fun atom approved result => by
      letI := original.decide atom approved result
      infer_instance)

theorem publication_exact_and_current
    (receipt : Invocation (publicationContract reviewed model schema before state pinned envelope)
      (ReviewedEffect.prepare reviewed model schema before ()) approved) :
    reviewed.advanceReviewed model schema before (fun _ _ => approved) = .ok receipt.result ∧
    state.current.world = pinned ∧ before.epoch = state.current.review.epoch := by
  have checked := receipt.logic
  change (ReviewedEffect.contract reviewed model schema before).meaning () approved receipt.result ∧
    before.epoch = state.current.review.epoch ∧ publicationGuard state pinned envelope = true at checked
  let original : Invocation (ReviewedEffect.contract reviewed model schema before)
      (ReviewedEffect.prepare reviewed model schema before ()) approved :=
    ⟨receipt.result, receipt.state, receipt.called, receipt.input, receipt.output, checked.1⟩
  exact ⟨ReviewedEffect.invocation_installs_exact_successor original,
    of_decide_eq_true (Bool.and_eq_true_iff.mp checked.2.2).1, checked.2.1⟩

theorem different_world_blocks_publication (state : State) (pinned envelope)
    (different : state.current.world ≠ pinned) : publicationGuard state pinned envelope = false := by
  simp [publicationGuard, different]

theorem invocation_is_exact
    (receipt : Invocation contract prepare
      (state,handle,envelope)) : receipt.result = use state handle envelope := receipt.logic

theorem accepted_retains_current (accepted : allowed state handle envelope = true) :
    accepts state.current envelope state.cedarAllowed = true := by
  exact (Bool.and_eq_true_iff.mp accepted).2

-- Historical permission and equal values never refresh the captured generation.
theorem old_handle_after_renew
    (state : State) (authority required world cedarAllowed envelope) :
    allowed (renew state authority required world cedarAllowed) (freshHandle state) envelope = false := by
  simp [allowed, freshHandle, renew, Handle.mk.injEq]

theorem old_handle_after_recovery (state : State) (committed complete envelope) :
    allowed (recover state committed complete) (freshHandle state) envelope = false := by
  simp [allowed, freshHandle, recover, Handle.mk.injEq]

theorem revoked_cannot_use (state : State) (handle envelope) :
    allowed (revoke state) handle envelope = false := by
  simp [allowed, revoke, accepts]

theorem recovery_preserves_revocation (state : State) (committed complete) :
    (recover state committed complete).current.revoked = state.current.revoked := rfl

theorem recovery_preserves_facts_and_clock (state : State) (committed complete) :
    (recover state committed complete).current.authority = state.current.authority ∧
    (recover state committed complete).factGeneration = state.factGeneration := ⟨rfl,rfl⟩

theorem recovery_preserves_burn (state : State) (committed complete)
    (spent : state.spent = true) :
    allowed (recover state committed complete) handle envelope = false := by
  simp [allowed, recover, spent]

theorem renewal_preserves_clock_and_controls (state : State) (authority required world cedarAllowed) :
    (renew state authority required world cedarAllowed).current.authority.now = state.current.authority.now ∧
    (renew state authority required world cedarAllowed).current.revoked = state.current.revoked ∧
    (renew state authority required world cedarAllowed).current.consumed = state.current.consumed ∧
    (renew state authority required world cedarAllowed).current.unknown = state.current.unknown ∧
    (renew state authority required world cedarAllowed).current.review.epoch = state.current.review.epoch :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem revoked_after_recovery_and_renewal (state : State) (committed complete authority required world cedarAllowed handle envelope) :
    allowed (renew (recover (revoke state) committed complete) authority required world cedarAllowed) handle envelope = false := by
  simp [allowed, renew, recover, revoke, accepts]

def invalidateSources (state : State) : State :=
  { state with sourcesCurrent := false, generation := state.generation + 1 }

theorem failed_refresh_blocks_use (state : State) (handle envelope) :
    allowed (invalidateSources state) handle envelope = false := by
  simp [allowed, invalidateSources]

theorem recovery_does_not_reopen_failed_sources (state : State) (committed complete handle envelope) :
    allowed (recover (invalidateSources state) committed complete) handle envelope = false := by
  simp [allowed, invalidateSources, recover]

theorem unresolved_without_commit_is_retained (state : State) (complete : Bool)
    (unknown : state.current.unknown = true) :
    (recover state false complete).current.unknown = true := by
  simp [recover, unknown]

theorem publication_requires_original_consumption (state : State) (pinned envelope)
    (missing : state.current.consumed = false) : publicationGuard state pinned envelope = false := by
  simp [publicationGuard, missing]

theorem spent_blocks_publication (state : State) (pinned envelope)
    (spent : state.spent = true) : publicationGuard state pinned envelope = false := by
  simp [publicationGuard, spent]

theorem fresh_use_is_actual_error_free
    {E S : Type} {project : E → S → Cedar.Spec.Request}
    {prepared : Gateway.Prepared E S project} {model : PolicyModules.Model}
    {effect : E} {view : S} {context : Gateway.Context} {checks : List Gateway.Assessment}
    {entities : Cedar.Spec.Entities}
    (receipt : Gateway.Receipt prepared model effect view context checks entities)
    (state : State) (bound : state.cedarAllowed = receipt.cedar.allowed)
    (accepted : allowed state handle envelope = true) :
    envelope.effect = state.current.effect ∧ envelope.review = state.current.review ∧
    Authorization.Delta.errorFreeAllow receipt.cedar.policies
      (Cedar.Spec.Env.mk (project effect view) entities) = true := by
  have current := accepted_retains_current accepted
  rw [bound] at current
  exact EffectProtocol.receipt_bound_effect_is_error_free receipt state.current envelope current
end CedarPooSpec.Gateway.Lifecycle
