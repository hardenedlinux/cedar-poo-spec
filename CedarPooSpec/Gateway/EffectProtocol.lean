import CedarPooSpec.ZeroTrust.Evidence
import CedarPooSpec.ZeroTrust.ProfileObject
import CedarPooSpec.Gateway.ZeroTrust

/-! Versioned current-effect contract and finite simulator. It owns no backend,
transport, credential store or alternate Cedar evaluator. Native adapters must
realize the independent readers and serialize all writers with effect use. -/
namespace CedarPooSpec.Gateway.EffectProtocol
open CedarPooSpec.ZeroTrust

structure Version where
  major : Nat := 1
  minor : Nat := 0
  deriving DecidableEq, BEq, Repr

def Version.supported (version : Version) : Bool := version == ⟨1, 0⟩

structure EffectIdentity where
  operation : String
  object : String
  generation : Nat
  payload : String
  actionSchema : String
  audience : String
  deriving DecidableEq, BEq, Repr

/-- The independent review authority supplies this record, not a candidate's
claim to have run an analyzer. Identical identities must name exact source bytes. -/
structure ReviewBinding where
  before : String
  after : String
  schema : String
  source : String
  epoch : Nat
  report : String
  deriving DecidableEq, BEq, Repr

structure Envelope where
  currentWorld : String
  version : Version
  effect : EffectIdentity
  review : ReviewBinding
  facts : List (FactBinding String String)
  deriving DecidableEq

structure Current where
  world : String
  effect : EffectIdentity
  review : ReviewBinding
  authority : FactAuthority String String
  required : List String
  enforcing : Bool
  mapped : Bool
  revoked : Bool
  registered : Bool
  consumed : Bool
  unknown : Bool

/-- Current source evidence must also name the world prepared by the SDK. -/
def currentEvidence (current : Current) (envelope : Envelope) : Bool :=
  (decide (envelope.currentWorld = current.world) &&
    current.authority.acceptsAll current.required envelope.facts) &&
    envelope.facts.all (fun fact => decide (fact.source = current.world))

/-- Caller input never selects the trusted current image. The actual Cedar
admission is supplied separately by the existing receipt/evaluator owner. -/
def accepts (current : Current) (envelope : Envelope) (cedarAllowed : Bool) : Bool :=
  envelope.version.supported && decide (envelope.effect = current.effect) &&
    decide (envelope.review = current.review) &&
    currentEvidence current envelope &&
    current.enforcing && current.mapped && !current.revoked && current.registered &&
    current.consumed && !current.unknown && cedarAllowed

private theorem false_of_negated (value : Bool) (negated : (!value) = true) : value = false := by
  cases value <;> simp_all

theorem accepted_effect_is_exact (current : Current) (envelope : Envelope)
    (cedarAllowed : Bool) (accepted : accepts current envelope cedarAllowed = true) :
    envelope.effect = current.effect ∧ envelope.review = current.review ∧
    current.authority.acceptsAll current.required envelope.facts = true ∧
    current.enforcing = true ∧ current.mapped = true ∧ current.revoked = false ∧
    current.registered = true ∧ current.consumed = true ∧ current.unknown = false ∧
    cedarAllowed = true := by
  have checked := accepted
  simp only [accepts, Bool.and_eq_true_iff, decide_eq_true_eq] at checked
  exact ⟨checked.1.1.1.1.1.1.1.1.1.2, checked.1.1.1.1.1.1.1.1.2,
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked.1.1.1.1.1.1.1.2).1).2, checked.1.1.1.1.1.1.2, checked.1.1.1.1.1.2,
    false_of_negated _ checked.1.1.1.1.2, checked.1.1.1.2, checked.1.1.2, false_of_negated _ checked.1.2, checked.2⟩

theorem accepted_world_is_current (current : Current) (envelope : Envelope)
    (accepted : accepts current envelope cedarAllowed = true) :
    envelope.currentWorld = current.world ∧
      ∀ fact ∈ envelope.facts, fact.source = current.world := by
  have checked := accepted
  simp only [accepts, Bool.and_eq_true_iff, decide_eq_true_eq] at checked
  have world := (Bool.and_eq_true_iff.mp checked.1.1.1.1.1.1.1.2).2
  have named := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked.1.1.1.1.1.1.1.2).1).1
  exact ⟨of_decide_eq_true named, by simpa [List.all_eq_true] using world⟩

/-- POO interpretation retains the supplied original requirement and adds the
actual evidence/effect check. Session/Contract remain with the existing owner. -/
def requirement (original : Requirement Envelope Current) : Requirement Envelope Current :=
  strengthen original (fun envelope current => accepts current envelope true = true)

theorem requirement_preserves_original (original : Requirement Envelope Current) :
    Refines original (requirement original) := strengthen_refines _ _

structure Outcome where
  admitted : Bool
  precommitted : Bool
  sent : Bool
  receipted : Bool
  unknown : Bool
  deriving DecidableEq, BEq, Repr

def Outcome.toJson (outcome : Outcome) : Lean.Json := Lean.Json.mkObj [
  ("admitted", Lean.toJson outcome.admitted), ("precommitted", Lean.toJson outcome.precommitted),
  ("sent", Lean.toJson outcome.sent), ("receipted", Lean.toJson outcome.receipted),
  ("unknown", Lean.toJson outcome.unknown)]

/-- Pure commit/send/outcome order; every native writer must share its boundary. -/
def Outcome.resolve (admitted logAvailable crashAfterSend : Bool) : Outcome :=
  let committed := admitted && logAvailable
  let complete := committed && !crashAfterSend
  ⟨admitted, committed, committed, complete, committed && !complete⟩

theorem send_requires_precommit (admitted logAvailable crashAfterSend : Bool) :
    (Outcome.resolve admitted logAvailable crashAfterSend).sent =
      (Outcome.resolve admitted logAvailable crashAfterSend).precommitted := rfl

theorem unknown_outcome_has_no_receipt (admitted logAvailable crashAfterSend : Bool)
    (unknown : (Outcome.resolve admitted logAvailable crashAfterSend).unknown = true) :
    (Outcome.resolve admitted logAvailable crashAfterSend).receipted = false := by
  have absent := (Bool.and_eq_true_iff.mp unknown).2
  exact false_of_negated _ absent

/-- Independently observed provider action. The verifier supplies this projection;
labels do not establish authenticity. -/
structure AuditRecord where
  operation : String
  value : String
  deriving DecidableEq, BEq, Repr

/-- Exact signed precommit bytes from the verified append-only history.
Operation names or digests alone are insufficient to identify a log entry. -/
structure CommitRef where
  operation : String
  payload : List UInt8
  signature : List UInt8
  deriving DecidableEq, BEq, Repr

/-- Verified outcome and its exact signed precommit, kept separate from the
provider observation. Cryptographic verification remains with the native owner. -/
structure AuditReceipt where
  action : AuditRecord
  commit : CommitRef
  deriving DecidableEq, BEq, Repr

structure AuditReport where
  unresolvedPrecommits : List String
  missingReceipts : List String
  missingActions : List String
  mismatched : List String
  duplicates : List String
  invalidReceipts : Nat
  invalidLog : Bool
  deriving DecidableEq, BEq, Repr

private def ids (items : List String) : List String :=
  items.eraseDups.mergeSort (fun a b => decide (a ≤ b))

/-- A receipt resolves only its exact commit and independently observed action. -/
def resolves (actions : List AuditRecord) (receipt : AuditReceipt) (commit : CommitRef) : Bool :=
  decide (receipt.commit = commit) && decide (receipt.action.operation = commit.operation) &&
    actions.any (fun action => decide (action = receipt.action))

theorem resolved_commit_is_exact (actions : List AuditRecord) (receipt : AuditReceipt)
    (commit : CommitRef) (resolved : resolves actions receipt commit = true) :
    receipt.commit = commit ∧ receipt.action.operation = commit.operation ∧
      receipt.action ∈ actions := by
  simpa [resolves, Bool.and_eq_true_iff, List.any_eq_true, and_assoc] using resolved

theorem different_commit_cannot_resolve (actions : List AuditRecord) (receipt : AuditReceipt)
    (commit : CommitRef) (different : receipt.commit ≠ commit) :
    resolves actions receipt commit = false := by
  simp [resolves, different]

def reconcile (actions : List AuditRecord) (receipts : List AuditReceipt)
    (invalid : Nat) (logValid : Bool) (precommits : List CommitRef := []) : AuditReport :=
  let actionIds := actions.map (·.operation)
  let receiptIds := receipts.map (·.action.operation)
  let commitIds := precommits.map (·.operation)
  let lastReceipts := receipts.foldr (fun receipt selected =>
    if selected.any (fun prior => prior.action.operation == receipt.action.operation) then selected else receipt :: selected) []
  { unresolvedPrecommits := ids ((precommits.filter (fun commit =>
      !(lastReceipts.any (fun receipt => resolves actions receipt commit)))).map (·.operation))
    missingReceipts := ids (actionIds.filter (fun name => !receiptIds.contains name))
    missingActions := ids (receiptIds.filter (fun name => !actionIds.contains name))
    mismatched := ids ((actions.filter fun action =>
      lastReceipts.any (fun receipt => receipt.action.operation == action.operation && receipt.action != action)).map (·.operation))
    duplicates := ids ((actionIds.filter (fun name => actionIds.count name > 1)) ++
      (receiptIds.filter (fun name => receiptIds.count name > 1)) ++
      commitIds.filter (fun name => commitIds.count name > 1))
    invalidReceipts := invalid
    invalidLog := !logValid }

/-- No outcome and no independent provider observation cannot erase a logged intent. -/
theorem precommit_without_observation_remains_unresolved (precommits : List CommitRef)
    (invalid : Nat) (logValid : Bool) (operation : String) :
    operation ∈ (reconcile [] [] invalid logValid precommits).unresolvedPrecommits ↔
      operation ∈ precommits.map (·.operation) := by
  simp [reconcile, ids]

theorem missing_receipt_iff (actions : List AuditRecord) (receipts : List AuditReceipt)
    (invalid : Nat) (logValid : Bool) (operation : String) :
    operation ∈ (reconcile actions receipts invalid logValid).missingReceipts ↔
      operation ∈ actions.map (·.operation) ∧ operation ∉ receipts.map (·.action.operation) := by
  simp [reconcile, ids]

theorem missing_action_iff (actions : List AuditRecord) (receipts : List AuditReceipt)
    (invalid : Nat) (logValid : Bool) (operation : String) :
    operation ∈ (reconcile actions receipts invalid logValid).missingActions ↔
      operation ∈ receipts.map (·.action.operation) ∧ operation ∉ actions.map (·.operation) := by
  simp [reconcile, ids]

theorem another_receipt_cannot_hide_precommit (actions : List AuditRecord)
    (receipt : AuditReceipt) (commit : CommitRef) (invalid : Nat) (logValid : Bool)
    (different : receipt.commit ≠ commit) :
    commit.operation ∈ (reconcile actions [receipt] invalid logValid [commit]).unresolvedPrecommits := by
  simp [reconcile, resolves, different, ids]

theorem duplicate_precommit_is_reported (earlier later : CommitRef)
    (same : earlier.operation = later.operation) :
    earlier.operation ∈ (reconcile [] [] 0 true [earlier, later]).duplicates := by
  simp [reconcile, ids, same]

/-- Recovery requires the entire independent audit to be clean, not merely a
matching operation label or the absence of signature errors. -/
def AuditReport.clean (report : AuditReport) : Bool :=
  decide (report = ⟨[], [], [], [], [], 0, false⟩)

/-- Projection of a detached provider-signed outcome after native decoding.
The signature interpretation is supplied by independently configured trust. -/
structure ProviderOutcome where
  version : Version
  domain : String
  logKey : String
  receipt : AuditReceipt
  signature : List UInt8
  deriving DecidableEq, BEq, Repr

structure ProviderAuditTrust where
  providerKey : String
  logKey : String
  authenticated : String → ProviderOutcome → Bool
  verified : FactAuthority String String → String → ProviderOutcome → Bool

/-- The native envelope interpretation checks the provider signature before
operation selection. Source semantics remain a separate historical check. -/
def ProviderAuditTrust.authenticates (trust : ProviderAuditTrust) (outcome : ProviderOutcome) : Bool :=
  trust.authenticated trust.providerKey outcome && outcome.version.supported &&
    decide (outcome.domain = "cedar-poo/provider-outcome") && decide (outcome.logKey = trust.logKey)

def ProviderAuditTrust.accepts (trust : ProviderAuditTrust) (source : FactAuthority String String)
    (outcome : ProviderOutcome) : Bool :=
  trust.authenticates outcome && trust.verified source trust.providerKey outcome

/-- Native interpretation verifies signatures and the original fact/publication
projection. This pure model does not claim a proof of cryptography or physical IO. -/
def reconcileProvider (trust : ProviderAuditTrust) (source : FactAuthority String String)
    (actions : List AuditRecord)
    (outcomes : List ProviderOutcome) (logValid : Bool) (precommits : List CommitRef) : AuditReport :=
  let accepted := outcomes.filter (trust.accepts source)
  reconcile actions (accepted.map (·.receipt)) (outcomes.length - accepted.length) logValid precommits

theorem accepted_provider_is_bound_to_configured_trust (trust : ProviderAuditTrust)
    (source : FactAuthority String String)
    (outcome : ProviderOutcome) (accepted : trust.accepts source outcome = true) :
    trust.authenticated trust.providerKey outcome = true ∧
      trust.verified source trust.providerKey outcome = true ∧ outcome.version.supported = true ∧
      outcome.domain = "cedar-poo/provider-outcome" ∧ outcome.logKey = trust.logKey := by
  simpa [ProviderAuditTrust.accepts, ProviderAuditTrust.authenticates, Bool.and_eq_true_iff, and_assoc, and_left_comm, and_comm] using accepted

theorem provider_without_outcomes_remains_unresolved (trust : ProviderAuditTrust)
    (source : FactAuthority String String)
    (actions : List AuditRecord) (logValid : Bool) (precommits : List CommitRef) (operation : String) :
    operation ∈ (reconcileProvider trust source actions [] logValid precommits).unresolvedPrecommits ↔
      operation ∈ precommits.map (·.operation) := by
  simp [reconcileProvider, reconcile, ids]

/-- Select one operation only after authentication. Invalid evidence and the
validity of the complete log remain independent, unfiltered obligations. -/
def reconcileOperation (operation : String) (actions : List AuditRecord)
    (receipts : List AuditReceipt) (invalid : Nat) (logValid : Bool)
    (precommits : List CommitRef) : AuditReport :=
  reconcile (actions.filter (fun action => decide (action.operation = operation)))
    (receipts.filter (fun receipt => decide (receipt.action.operation = operation)))
    invalid logValid (precommits.filter (fun entry => decide (entry.operation = operation)))

theorem unrelated_precommit_preserves_operation_report (operation : String)
    (actions : List AuditRecord) (receipts : List AuditReceipt) (invalid : Nat)
    (logValid : Bool) (precommits : List CommitRef) (foreign : CommitRef)
    (different : foreign.operation ≠ operation) :
    reconcileOperation operation actions receipts invalid logValid (precommits ++ [foreign]) =
      reconcileOperation operation actions receipts invalid logValid precommits := by
  simp [reconcileOperation, List.filter_append, different]

/-- A scoped result uses one independently retained exact intent. It still
requires the full log-validity premise and authenticates every outcome envelope
and its membership before selecting the operation's source interpretation. -/
def reconcileProviderIntent (trust : ProviderAuditTrust) (source : FactAuthority String String)
    (intent : CommitRef) (actions : List AuditRecord) (outcomes : List ProviderOutcome)
    (logValid : Bool) (precommits : List CommitRef) : AuditReport :=
  let authenticated := outcomes.filter (fun outcome => trust.authenticates outcome &&
    (precommits.any (fun entry => decide (entry = outcome.receipt.commit))) &&
    decide (outcome.receipt.action.operation = outcome.receipt.commit.operation))
  let relevant := authenticated.filter (fun outcome => decide (outcome.receipt.action.operation = intent.operation))
  let accepted := relevant.filter (trust.accepts source)
  reconcileOperation intent.operation actions (accepted.map (·.receipt))
    (outcomes.length - authenticated.length + relevant.length - accepted.length)
    (logValid && (precommits.any (fun entry => decide (entry = intent)))) precommits

theorem scoped_invalid_log_is_not_hidden (trust : ProviderAuditTrust) (source : FactAuthority String String)
    (intent : CommitRef) (actions : List AuditRecord) (outcomes : List ProviderOutcome)
    (precommits : List CommitRef) :
    (reconcileProviderIntent trust source intent actions outcomes false precommits).invalidLog = true := by
  simp [reconcileProviderIntent, reconcileOperation, reconcile]

theorem scoped_missing_anchor_is_invalid (trust : ProviderAuditTrust) (source : FactAuthority String String)
    (intent : CommitRef) (actions : List AuditRecord) (outcomes : List ProviderOutcome)
    (precommits : List CommitRef) (missing : intent ∉ precommits) :
    (reconcileProviderIntent trust source intent actions outcomes true precommits).invalidLog = true := by
  have absent : precommits.any (fun entry => decide (entry = intent)) = false := by
    apply Bool.eq_false_iff.mpr
    simpa [List.any_eq_true] using missing
  simp [reconcileProviderIntent, reconcileOperation, reconcile, absent]

theorem scoped_bad_envelope_is_not_ignored (trust : ProviderAuditTrust) (source : FactAuthority String String)
    (intent : CommitRef) (actions : List AuditRecord) (outcome : ProviderOutcome)
    (precommits : List CommitRef) (bad : trust.authenticates outcome = false) :
    (reconcileProviderIntent trust source intent actions [outcome] true precommits).invalidReceipts = 1 := by
  simp [reconcileProviderIntent, reconcileOperation, reconcile, bad]

theorem scoped_same_operation_precommits_are_reported
    (trust : ProviderAuditTrust) (source : FactAuthority String String) (intent other : CommitRef)
    (same : other.operation = intent.operation) :
    intent.operation ∈ (reconcileProviderIntent trust source intent [] [] true [intent, other]).duplicates := by
  simp [reconcileProviderIntent, reconcileOperation, reconcile, ids, same]

structure LineageEdge where
  source : String
  operation : String
  providerObserved : Bool
  deriving DecidableEq, BEq, Repr

/-- Lineage describes evidence dependencies, never an authorization decision. -/
def affected (edges : List LineageEdge) (sources : List String) : List String :=
  ((edges.filter (fun edge => decide (edge.source ∈ sources))).map (·.operation)).eraseDups

theorem affected_iff (edges : List LineageEdge) (sources : List String) (operation : String) :
    operation ∈ affected edges sources ↔
      ∃ edge ∈ edges, edge.operation = operation ∧ edge.source ∈ sources := by
  simp [affected, and_assoc, and_left_comm, and_comm]

/-- Join the protocol to the existing typed admission receipt. The protocol
cannot manufacture Cedar Allow, schema validity or an execution capability. -/
theorem receipt_bound_effect_is_error_free
    {E S : Type} {project : E → S → Cedar.Spec.Request}
    {prepared : Gateway.Prepared E S project} {model : PolicyModules.Model}
    {effect : E} {state : S} {context : Gateway.Context}
    {checks : List Gateway.Assessment} {entities : Cedar.Spec.Entities}
    (receipt : Gateway.Receipt prepared model effect state context checks entities)
    (current : Current) (envelope : Envelope)
    (accepted : accepts current envelope receipt.cedar.allowed = true) :
    envelope.effect = current.effect ∧ envelope.review = current.review ∧
      Authorization.Delta.errorFreeAllow receipt.cedar.policies
        (Cedar.Spec.Env.mk (project effect state) entities) = true := by
  have bound := accepted_effect_is_exact current envelope receipt.cedar.allowed accepted
  exact ⟨bound.1, bound.2.1, Gateway.admitted_actual_request_is_error_free receipt⟩

end CedarPooSpec.Gateway.EffectProtocol
