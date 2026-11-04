import CedarPooSpec.Gateway.ReviewedEffect

/-! Current-use safety after source renewal, revocation and mediator recovery.
The Host must supply the actual current image and realize its atomic writers.
Historical publication approval is not a fresh-world Cedar receipt. -/
namespace CedarPooSpec.Gateway.Lifecycle
open EffectProtocol LeanPoo.Functional.DeclarativeMetadata

/-- Exact intent retained by the trusted deciding writer before provider use. -/
structure RetainedIntent where
  commit : CommitRef
  logKey : String
  deriving DecidableEq, BEq, Repr

/-- Verified public history and independent audit/provider projections.
Native signature verification supplies these projections, not caller labels. -/
structure RecoveryEvidence where
  entries : List CommitRef
  logKey : String
  report : AuditReport
  observed : Bool
  deriving DecidableEq, BEq, Repr

structure RecoveryInput where
  operation : String
  retained : Option RetainedIntent
  evidence : RecoveryEvidence
  deriving DecidableEq, BEq, Repr

structure RecoveryStatus where
  committed : Bool
  complete : Bool
  deriving DecidableEq, BEq, Repr

/-- Clean historical evidence cannot substitute for the surviving intent. -/
def checkRecovery (input : RecoveryInput) : Except String RecoveryStatus :=
  if input.evidence.report.invalidLog then .error "invalid history"
  else match input.retained with
  | some retained =>
    if input.evidence.logKey == retained.logKey &&
        input.evidence.entries.any (fun entry => decide (entry = retained.commit)) then
      .ok ⟨true, input.evidence.observed && input.evidence.report.clean⟩
    else .error "missing retained intent"
  | none =>
    if input.evidence.entries.any (fun entry => entry.operation == input.operation) then
      .error "unrecorded operation intent"
    else .ok ⟨false, false⟩

def recoveryContract : Contract Unit RecoveryInput RecoveryStatus where
  input := ⟨"retained-recovery-evidence", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"bound-recovery-status", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => checkRecovery input = .ok result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareRecovery (input : RecoveryInput) : Except String (RecoveryStatus × Unit) := do
  let checked ← checkRecovery input
  pure (checked, ())

theorem recovery_invocation_is_bound
    (receipt : Invocation recoveryContract prepareRecovery input) :
    checkRecovery input = .ok receipt.result := receipt.logic

/-- Compact authenticated progress. Native code uses the boundary's complete
signed-pair digest under collision resistance and the full verified chain. -/
structure WitnessFrontier where
  logKey : String
  size : Nat
  boundary : Option CommitRef
  deriving DecidableEq, BEq, Repr

def WitnessFrontier.observe (logKey : String) (entries : List CommitRef) : WitnessFrontier :=
  ⟨logKey, entries.length, entries.getLast?⟩

/-- Read the checked boundary directly without allocating a copied prefix. -/
def WitnessFrontier.boundaryAt (size : Nat) (entries : List CommitRef) : Option CommitRef :=
  if size = 0 then none else entries[size - 1]?

theorem indexed_boundary_matches_verified_prefix (size : Nat) (entries : List CommitRef)
    (within : size ≤ entries.length) :
    WitnessFrontier.boundaryAt size entries = (entries.take size).getLast? := by
  rw [List.getLast?_take]
  unfold WitnessFrontier.boundaryAt
  split
  · rfl
  · have available : size - 1 < entries.length := by omega
    simp only [List.getElem?_eq_getElem available, Option.some_or]

def WitnessFrontier.extends (prior : WitnessFrontier) (logKey : String)
    (entries : List CommitRef) : Bool :=
  decide (prior.logKey = logKey) && decide (prior.size ≤ entries.length) &&
    decide (WitnessFrontier.boundaryAt prior.size entries = prior.boundary)

structure HistoryInput where
  prior : Option WitnessFrontier
  logKey : String
  entries : List CommitRef
  valid : Bool
  independent : Option WitnessFrontier := none

def checkHistory (input : HistoryInput) : Except String WitnessFrontier :=
  if input.valid && input.prior.all (fun prior => prior.extends input.logKey input.entries) &&
      input.independent.all (fun pin => pin.extends input.logKey input.entries) then
    .ok (WitnessFrontier.observe input.logKey input.entries)
  else .error "witness frontier regressed or changed prefix"

def historyContract : Contract Unit HistoryInput WitnessFrontier where
  input := ⟨"verified-history-extension", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"retained-witness-frontier", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => checkHistory input = .ok result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareHistory (input : HistoryInput) : Except String (WitnessFrontier × Unit) := do
  pure (← checkHistory input, ())

theorem history_invocation_is_bound
    (receipt : Invocation historyContract prepareHistory input) :
    checkHistory input = .ok receipt.result := receipt.logic

theorem rollback_frontier_is_refused (prior : WitnessFrontier) (logKey : String)
    (entries : List CommitRef) (valid : Bool) (shorter : entries.length < prior.size) :
    (checkHistory ⟨some prior, logKey, entries, valid, none⟩).isOk = false := by
  simp [checkHistory, WitnessFrontier.extends, Nat.not_le_of_lt shorter, Except.isOk, Except.toBool]

theorem changed_frontier_is_refused (prior : WitnessFrontier) (logKey : String)
    (entries : List CommitRef) (valid : Bool)
    (changed : (entries.take prior.size).getLast? ≠ prior.boundary) :
    (checkHistory ⟨some prior, logKey, entries, valid, none⟩).isOk = false := by
  by_cases within : prior.size ≤ entries.length
  · have bound := indexed_boundary_matches_verified_prefix prior.size entries within
    simp [checkHistory, WitnessFrontier.extends, bound, changed, Except.isOk, Except.toBool]
  · simp [checkHistory, WitnessFrontier.extends, within, Except.isOk, Except.toBool]

theorem history_result_retains_observed_frontier
    (receipt : Invocation historyContract prepareHistory input) :
    receipt.result = WitnessFrontier.observe input.logKey input.entries := by
  have bound := history_invocation_is_bound receipt
  simp only [checkHistory] at bound
  split at bound
  · exact (Except.ok.inj bound).symm
  · cases bound

theorem changed_witness_key_is_refused (prior : WitnessFrontier) (logKey : String)
    (entries : List CommitRef) (valid : Bool) (changed : prior.logKey ≠ logKey) :
    (checkHistory ⟨some prior, logKey, entries, valid, none⟩).isOk = false := by
  simp [checkHistory, WitnessFrontier.extends, changed, Except.isOk, Except.toBool]

/-- An independent pin is required alongside, rather than replaced by, the
surviving local prefix. A valid signature flag cannot bypass either boundary. -/
theorem history_invocation_extends_independent
    (receipt : Invocation historyContract prepareHistory input)
    (configured : input.independent = some pin) :
    pin.extends input.logKey input.entries = true := by
  have bound := history_invocation_is_bound receipt
  cases accepted : pin.extends input.logKey input.entries
  · simp [checkHistory, configured, accepted] at bound
  · rfl

theorem same_length_fork_refused (prior : Option WitnessFrontier) (pin : WitnessFrontier)
    (logKey : String) (entries : List CommitRef) (valid : Bool)
    (sameSize : pin.size = entries.length)
    (differentHead : WitnessFrontier.boundaryAt entries.length entries ≠ pin.boundary) :
    (checkHistory ⟨prior, logKey, entries, valid, some pin⟩).isOk = false := by
  have different : WitnessFrontier.boundaryAt pin.size entries ≠ pin.boundary := by
    simpa only [sameSize] using differentHead
  simp [checkHistory, WitnessFrontier.extends, different,
    Except.isOk, Except.toBool]

structure State where
  current : Current
  generation : Nat := 0
  owner : Nat := 0
  factGeneration : Nat := 7
  spent : Bool := false
  witnessFrontier : Option WitnessFrontier := none
  retainedIntent : Option RetainedIntent := none
  retainedAuthority : Option (CedarPooSpec.ZeroTrust.FactAuthority String String) := none
  sourcesCurrent : Bool := true
  publicationUnknown : Bool := false
  cedarAllowed : Bool

/-- Mirror the deciding precommit write: source interpretation, exact intent,
consumption and uncertainty belong to the same surviving authority update. -/
def retainIntent (state : State) (intent : RetainedIntent) : State :=
  { state with
    retainedIntent := some intent
    retainedAuthority := some state.current.authority
    spent := true
    current := { state.current with unknown := true } }

theorem retained_source_is_original (state : State) (intent : RetainedIntent) :
    (retainIntent state intent).retainedAuthority = some state.current.authority := rfl

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

/-- Install progress in the same transition that rotates the mediator owner. -/
def recoverObserved (state : State) (status : RecoveryStatus) (frontier : WitnessFrontier) : State :=
  {recover state status.committed status.complete with witnessFrontier := some frontier}

theorem observed_recovery_retains_verified_progress (state : State) (status : RecoveryStatus)
    (receipt : Invocation historyContract prepareHistory input) :
    (recoverObserved state status receipt.result).witnessFrontier =
      some (WitnessFrontier.observe input.logKey input.entries) := by
  simp only [recoverObserved, history_result_retains_observed_frontier receipt]

theorem observed_recovery_preserves_current_authority (state : State) (status : RecoveryStatus)
    (frontier : WitnessFrontier) :
    (recoverObserved state status frontier).current.authority = state.current.authority ∧
    (recoverObserved state status frontier).current.revoked = state.current.revoked ∧
    (recoverObserved state status frontier).retainedAuthority = state.retainedAuthority ∧
    (recoverObserved state status frontier).sourcesCurrent = state.sourcesCurrent ∧
    (recoverObserved state status frontier).spent = (state.spent || status.committed) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Compose verified reconciliation with recovery. The independent provider
must also observe the exact retained effect; current authorization is preserved. -/
def recoverAudited (state : State) (committed observed : Bool) (report : AuditReport) : State :=
  recover state committed (observed && report.clean)

theorem unclean_audit_retains_unknown (state : State) (committed observed : Bool)
    (report : AuditReport) (unclean : report.clean = false)
    (unknown : state.current.unknown = true) :
    (recoverAudited state committed observed report).current.unknown = true := by
  simp [recoverAudited, recover, unclean, unknown]

theorem audited_recovery_preserves_burn (state : State) (committed observed : Bool)
    (report : AuditReport) (spent : state.spent = true) :
    (recoverAudited state committed observed report).spent = true := by
  simp [recoverAudited, recover, spent]

/-- Recovery consumes the actual retained-state Contract, then rotates ownership. -/
def recoverChecked (state : State) (evidence : RecoveryEvidence)
    (independent : Option WitnessFrontier := none) : Except String State := do
  let history ← (historyContract.invoke prepareHistory
    ⟨state.witnessFrontier, evidence.logKey, evidence.entries, !evidence.report.invalidLog, independent⟩).mapError
      (fun _ => "history extension Contract refused")
  let receipt ← (recoveryContract.invoke prepareRecovery
    ⟨state.current.effect.operation, state.retainedIntent, evidence⟩).mapError
      (fun _ => "retained recovery Contract refused")
  pure (recoverObserved state receipt.result history.result)

structure ProviderRecoveryEvidence where
  actions : List AuditRecord
  outcomes : List ProviderOutcome
  entries : List CommitRef
  logValid : Bool
  expected : AuditRecord

private def providerEvidence (trust : ProviderAuditTrust)
    (source : CedarPooSpec.ZeroTrust.FactAuthority String String)
    (intent : CommitRef) (evidence : ProviderRecoveryEvidence) : RecoveryEvidence :=
  ⟨evidence.entries, trust.logKey,
    reconcileProviderIntent trust source intent evidence.actions evidence.outcomes evidence.logValid evidence.entries,
    evidence.actions.any (fun action => decide (action = evidence.expected))⟩

def checkProviderRecovery (trust : ProviderAuditTrust) (state : State)
    (evidence : ProviderRecoveryEvidence) : Except String RecoveryStatus :=
  match state.retainedAuthority with
  | none => .error "missing retained source authority"
  | some source =>
    if evidence.expected.operation != state.current.effect.operation then .error "different operation"
    else match state.retainedIntent with
    | none => .error "missing retained intent"
    | some retained => checkRecovery ⟨state.current.effect.operation, state.retainedIntent,
        providerEvidence trust source retained.commit evidence⟩

def providerRecoveryContract (trust : ProviderAuditTrust) :
    Contract Unit (State × ProviderRecoveryEvidence) RecoveryStatus where
  input := ⟨"independent-provider-recovery", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"bound-provider-completion", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => checkProviderRecovery trust input.1 input.2 = .ok result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareProviderRecovery (trust : ProviderAuditTrust) (input : State × ProviderRecoveryEvidence) :
    Except String (RecoveryStatus × Unit) := do
  let checked ← checkProviderRecovery trust input.1 input.2
  pure (checked, ())

def recoverFromProviderChecked (trust : ProviderAuditTrust) (state : State)
    (evidence : ProviderRecoveryEvidence) (independent : Option WitnessFrontier := none) :
    Except String State := do
  let history ← (historyContract.invoke prepareHistory
    ⟨state.witnessFrontier, trust.logKey, evidence.entries, evidence.logValid, independent⟩).mapError
      (fun _ => "provider history extension Contract refused")
  let receipt ← ((providerRecoveryContract trust).invoke (prepareProviderRecovery trust)
    (state, evidence)).mapError (fun _ => "provider recovery Contract refused")
  pure (recoverObserved state receipt.result history.result)

theorem provider_recovery_invocation_is_bound
    (receipt : Invocation (providerRecoveryContract trust) (prepareProviderRecovery trust) (state, evidence)) :
    checkProviderRecovery trust state evidence = .ok receipt.result := receipt.logic

theorem missing_retained_intent_is_refused (operation : String) (retained : RetainedIntent)
    (evidence : RecoveryEvidence)
    (missing : evidence.entries.any (fun entry => decide (entry = retained.commit)) = false) :
    (checkRecovery ⟨operation, some retained, evidence⟩).isOk = false := by
  cases h : evidence.report.invalidLog <;> simp [checkRecovery, h, missing, Except.isOk, Except.toBool]

theorem foreign_log_key_is_refused (operation : String) (retained : RetainedIntent)
    (evidence : RecoveryEvidence) (different : evidence.logKey ≠ retained.logKey) :
    (checkRecovery ⟨operation, some retained, evidence⟩).isOk = false := by
  cases h : evidence.report.invalidLog <;> simp [checkRecovery, h, different, Except.isOk, Except.toBool]

theorem retained_recovery_requires_exact_history (operation : String) (retained : RetainedIntent)
    (evidence : RecoveryEvidence) (status : RecoveryStatus)
    (accepted : checkRecovery ⟨operation, some retained, evidence⟩ = .ok status) :
    evidence.logKey = retained.logKey ∧ retained.commit ∈ evidence.entries := by
  simp only [checkRecovery] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · rename_i matched
      simpa [Bool.and_eq_true_iff, List.any_eq_true] using matched
    · cases accepted

theorem renewal_preserves_retained_intent (state : State) (authority required world cedarAllowed) :
    (renew state authority required world cedarAllowed).retainedIntent = state.retainedIntent := rfl

theorem recovery_preserves_retained_intent (state : State) (committed complete) :
    (recover state committed complete).retainedIntent = state.retainedIntent := rfl

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

theorem provider_recovery_exact_retained_history
    (state : State) (evidence : ProviderRecoveryEvidence) (trust : ProviderAuditTrust)
    (retained : RetainedIntent) (present : state.retainedIntent = some retained)
    (receipt : Invocation (providerRecoveryContract trust) (prepareProviderRecovery trust) (state, evidence)) :
    trust.logKey = retained.logKey ∧ retained.commit ∈ evidence.entries := by
  have checked := provider_recovery_invocation_is_bound receipt
  cases source : state.retainedAuthority with
  | none => simp [checkProviderRecovery, source] at checked
  | some historical =>
    simp only [checkProviderRecovery, source, present] at checked
    split at checked
    · cases checked
    · exact retained_recovery_requires_exact_history state.current.effect.operation retained
        (providerEvidence trust historical retained.commit evidence) receipt.result (by simpa [present] using checked)

theorem provider_settlement_does_not_remint
    (receipt : Invocation (providerRecoveryContract trust) (prepareProviderRecovery trust) (state, evidence))
    (spent : state.spent = true) :
    allowed (recover state receipt.result.committed receipt.result.complete) handle envelope = false :=
  recovery_preserves_burn state _ _ spent
theorem provider_settlement_preserves_current_image
    (receipt : Invocation (providerRecoveryContract trust) (prepareProviderRecovery trust) (state, evidence)) :
    (recover state receipt.result.committed receipt.result.complete).current.effect = state.current.effect ∧
    (recover state receipt.result.committed receipt.result.complete).current.mapped = state.current.mapped ∧
    (recover state receipt.result.committed receipt.result.complete).current.revoked = state.current.revoked ∧
    (recover state receipt.result.committed receipt.result.complete).current.authority = state.current.authority :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem missing_retained_source_is_refused (trust : ProviderAuditTrust) (state : State)
    (evidence : ProviderRecoveryEvidence) (missing : state.retainedAuthority = none) :
    (checkProviderRecovery trust state evidence).isOk = false := by
  simp [checkProviderRecovery, missing, Except.isOk, Except.toBool]

theorem provider_recovery_is_independent_of_current_authority (trust : ProviderAuditTrust)
    (state : State) (evidence : ProviderRecoveryEvidence)
    (current : CedarPooSpec.ZeroTrust.FactAuthority String String) :
    checkProviderRecovery trust {state with current := {state.current with authority := current}} evidence =
      checkProviderRecovery trust state evidence := rfl

theorem renewal_preserves_retained_source (state : State) (authority required world cedarAllowed) :
    (renew state authority required world cedarAllowed).retainedAuthority = state.retainedAuthority := rfl

theorem provider_settlement_preserves_source_views
    (receipt : Invocation (providerRecoveryContract trust) (prepareProviderRecovery trust) (state, evidence)) :
    (recover state receipt.result.committed receipt.result.complete).retainedAuthority = state.retainedAuthority ∧
    (recover state receipt.result.committed receipt.result.complete).sourcesCurrent = state.sourcesCurrent ∧
    (recover state receipt.result.committed receipt.result.complete).factGeneration = state.factGeneration :=
  ⟨rfl, rfl, rfl⟩

/-- The simulator's maintenance transitions. A rejected clock rollback
stutters. Settlement uses the projection of an independently checked recovery. -/
inductive Maintenance where
  | tick (now : Nat)
  | renewFacts (authority : CedarPooSpec.ZeroTrust.FactAuthority String String)
      (required : List String) (world : String) (cedarAllowed : Bool)
  | invalidate
  | settle (status : RecoveryStatus) (frontier : WitnessFrontier)

def Maintenance.apply (state : State) : Maintenance → State
  | .tick now =>
    if state.current.authority.now ≤ now then
      let authority := { state.current.authority with now := now }
      { state with
        current := { state.current with authority := authority }
        generation := state.generation + 1 }
    else state
  | .renewFacts authority required world cedarAllowed => renew state authority required world cedarAllowed
  | .invalidate => invalidateSources state
  | .settle status frontier => recoverObserved state status frontier

theorem maintenance_preserves_revocation (state : State) (step : Maintenance) :
    (step.apply state).current.revoked = state.current.revoked := by
  cases step <;> simp [Maintenance.apply, renew, invalidateSources, recoverObserved, recover, apply_ite]

theorem maintenance_preserves_burn (state : State) (step : Maintenance)
    (burned : state.spent = true) : (step.apply state).spent = true := by
  cases step <;> simp [Maintenance.apply, renew, invalidateSources, recoverObserved, recover, apply_ite, burned]

/-- Terminal revocation survives any finite sequence of maintenance writes.
The endpoint refuses both fresh effect use and reviewed Delta publication. -/
theorem revoked_trace_blocks_use_and_publication (state : State) (steps : List Maintenance)
    (revoked : state.current.revoked = true) (handle : Handle) (pinned : String)
    (envelope : Envelope) :
    let final := steps.foldl (fun s step => step.apply s) state
    allowed final handle envelope = false ∧ publicationGuard final pinned envelope = false := by
  induction steps generalizing state with
  | nil =>
    exact ⟨by simp [allowed, accepts, revoked], by simp [publicationGuard, revoked]⟩
  | cons step rest ih =>
    exact ih (step.apply state) ((maintenance_preserves_revocation state step).trans revoked)

/-- Maintenance cannot turn reconciliation into a second execution right. -/
theorem burned_trace_stays_burned (state : State) (steps : List Maintenance)
    (burned : state.spent = true) :
    (steps.foldl (fun s step => step.apply s) state).spent = true := by
  induction steps generalizing state with
  | nil => exact burned
  | cons step rest ih => exact ih (step.apply state) (maintenance_preserves_burn state step burned)

end CedarPooSpec.Gateway.Lifecycle
