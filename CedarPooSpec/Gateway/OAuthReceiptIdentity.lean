import CedarPooSpec.Gateway.OAuthReceiver

/-! Native decoders select independently verified sources. The mapping keeps
exact source bytes as well as their host-computed digests. -/
namespace CedarPooSpec.Gateway.OAuth.ReceiptIdentity
open Gateway.EffectProtocol LeanPoo.Functional.DeclarativeMetadata

structure SignedSource where
  payload : List UInt8
  signature : List UInt8
  deriving DecidableEq

structure CanonicalReceipt where
  symbolic : ProviderOutcome
  intent : CommitRef
  intentSource : SignedSource
  outcomeSource : SignedSource

structure Authority where
  receiver : Revocation.Crash.ReceiverBinding
  providerKey : String
  witnessKey : String
  read : String → Option CanonicalReceipt
  digest : SignedSource → String

structure Identity where
  receiver : Revocation.Crash.ReceiverBinding
  providerKey : String
  witnessKey : String
  operation : String
  intentDigest : String
  outcomeDigest : String
  version : Version := {}
  deriving DecidableEq

structure Request where
  symbolic : ProviderOutcome
  operation : String
  identity : Identity
  intentSource : SignedSource
  outcomeSource : SignedSource

def project (authority : Authority) (operation : String) (source : CanonicalReceipt) : Identity :=
  { receiver := authority.receiver, providerKey := authority.providerKey, witnessKey := authority.witnessKey, operation
    intentDigest := authority.digest source.intentSource
    outcomeDigest := authority.digest source.outcomeSource }

def corresponds (authority : Authority) (request : Request) (source : CanonicalReceipt) : Prop :=
  request.identity = project authority request.operation source ∧
    request.intentSource = source.intentSource ∧ request.outcomeSource = source.outcomeSource ∧
    request.symbolic = source.symbolic ∧ source.symbolic.receipt.commit.operation = request.operation ∧
    source.intent = source.symbolic.receipt.commit ∧
    source.symbolic.receipt.action.operation = request.operation ∧
    source.symbolic.version.supported = true ∧ source.symbolic.domain = "cedar-poo/provider-outcome" ∧
    source.symbolic.logKey = authority.witnessKey

instance : Decidable (corresponds authority request source) := by
  unfold corresponds
  infer_instance

def resolve (authority : Authority) (request : Request) : Option Identity := do
  let source ← authority.read request.operation
  if corresponds authority request source then some request.identity else none

def contract : Contract Unit (Authority × Request) Identity where
  input := ⟨"trusted-decoder-and-independent-receipt-source", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"operation-authority-and-exact-source-bound-identity", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => resolve input.1 input.2 = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : Authority × Request) : Except String (Identity × Unit) :=
  match resolve input.1 input.2 with
  | some result => .ok (result, ())
  | none => .error "receipt identity mapping refused"

theorem accepted_mapping
    (receipt : Invocation contract prepare (authority, request)) :
    ∃ source, authority.read request.operation = some source ∧
      corresponds authority request source ∧ receipt.result = request.identity := by
  have accepted := receipt.logic
  change resolve authority request = some receipt.result at accepted
  cases found : authority.read request.operation with
  | none => simp [resolve, found] at accepted
  | some source =>
    simp only [resolve, found, bind, Option.bind] at accepted
    split at accepted
    · rename_i matched
      exact ⟨source, rfl, matched, (Option.some.inj accepted).symm⟩
    · contradiction

theorem wrong_operation_refused (wrong : request.identity.operation ≠ request.operation) :
    resolve authority request = none := by
  cases found : authority.read request.operation with
  | none => simp [resolve, found]
  | some source =>
    have refused : ¬ corresponds authority request source := by
      intro accepted
      exact wrong (congrArg Identity.operation accepted.1)
    simp [resolve, found, refused]

theorem wrong_symbolic_operation_refused
    (wrong : request.symbolic.receipt.commit.operation ≠ request.operation) :
    resolve authority request = none := by
  cases found : authority.read request.operation with
  | none => simp [resolve, found]
  | some source =>
    have refused : ¬ corresponds authority request source := by
      intro accepted
      have symbolic := accepted.2.2.2.1
      have operation := accepted.2.2.2.2.1
      apply wrong
      simpa [symbolic] using operation
    simp [resolve, found, refused]

theorem foreign_receiver_refused (wrong : request.identity.receiver ≠ authority.receiver) :
    resolve authority request = none := by
  cases found : authority.read request.operation with
  | none => simp [resolve, found]
  | some source =>
    have refused : ¬ corresponds authority request source := by
      intro accepted
      exact wrong (congrArg Identity.receiver accepted.1)
    simp [resolve, found, refused]

theorem foreign_provider_refused (wrong : request.identity.providerKey ≠ authority.providerKey) :
    resolve authority request = none := by
  cases found : authority.read request.operation with
  | none => simp [resolve, found]
  | some source =>
    have refused : ¬ corresponds authority request source := by
      intro accepted
      exact wrong (congrArg Identity.providerKey accepted.1)
    simp [resolve, found, refused]

theorem foreign_witness_refused (wrong : request.identity.witnessKey ≠ authority.witnessKey) :
    resolve authority request = none := by
  cases found : authority.read request.operation with
  | none => simp [resolve, found]
  | some source =>
    have refused : ¬ corresponds authority request source := by
      intro accepted
      exact wrong (congrArg Identity.witnessKey accepted.1)
    simp [resolve, found, refused]

theorem changed_source_refused (found : authority.read request.operation = some source)
    (changed : request.outcomeSource ≠ source.outcomeSource) :
    resolve authority request = none := by
  have refused : ¬ corresponds authority request source := fun accepted => changed accepted.2.2.1
  simp [resolve, found, refused]

theorem changed_intent_refused (found : authority.read request.operation = some source)
    (changed : request.intentSource ≠ source.intentSource) :
    resolve authority request = none := by
  have refused : ¬ corresponds authority request source := fun accepted => changed accepted.2.1
  simp [resolve, found, refused]


/-- A model receipt is scoped by its complete operation and authority frame. -/
structure ReceiptSymbol where
  receipt : ProviderOutcome
  receiver : Revocation.Crash.ReceiverBinding
  providerKey : String
  witnessKey : String
  operation : String
  version : Version
  deriving DecidableEq

def Request.receiptSymbol (request : Request) : ReceiptSymbol :=
  ⟨request.symbolic, request.identity.receiver, request.identity.providerKey,
    request.identity.witnessKey, request.identity.operation, request.identity.version⟩

def ReceiptSymbol.matches (symbol : ReceiptSymbol) (identity : Identity)
    (receipt : ProviderOutcome) : Prop :=
  symbol.receipt = receipt ∧ symbol.operation = identity.operation ∧
  symbol.receiver = identity.receiver ∧ symbol.providerKey = identity.providerKey ∧
  symbol.witnessKey = identity.witnessKey ∧ symbol.version = identity.version

instance : Decidable (ReceiptSymbol.matches symbol identity receipt) := by
  unfold ReceiptSymbol.matches
  infer_instance

/-- The native digests are claims about these exact sources, not replacements for them. -/
structure Realization where
  symbol : ReceiptSymbol
  native : Identity
  intentSource : SignedSource
  outcomeSource : SignedSource
  deriving DecidableEq

def Realization.select (symbol : ReceiptSymbol) (native : Identity)
    (receipt : ProviderOutcome) (intentSource outcomeSource : SignedSource) : Option Realization :=
  if symbol.matches native receipt then some ⟨symbol, native, intentSource, outcomeSource⟩ else none

def Realization.check (expected candidate : Realization) : Option Identity :=
  if candidate = expected then some expected.native else none

def realize (authority : Authority) (request : Request) (symbol : ReceiptSymbol) : Option Realization := do
  let native ← resolve authority request
  Realization.select symbol native request.symbolic request.intentSource request.outcomeSource

def realizationContract : Contract Unit (Authority × Request × ReceiptSymbol) Realization where
  input := ⟨"verified-decoder-and-scoped-symbolic-receipt", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"exact-symbol-native-identity-and-signed-sources", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => realize input.1 input.2.1 input.2.2 = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareRealization (input : Authority × Request × ReceiptSymbol) :
    Except String (Realization × Unit) :=
  match realize input.1 input.2.1 input.2.2 with
  | some result => .ok (result, ())
  | none => .error "symbolic receipt realization refused"

theorem resolved_identity (accepted : resolve authority request = some native) :
    native = request.identity := by
  cases found : authority.read request.operation with
  | none => simp [resolve, found] at accepted
  | some source =>
    simp only [resolve, found, bind, Option.bind] at accepted
    split at accepted
    · exact (Option.some.inj accepted).symm
    · contradiction

theorem resolved_source_digests (accepted : resolve authority request = some native) :
    native.intentDigest = authority.digest request.intentSource ∧
    native.outcomeDigest = authority.digest request.outcomeSource := by
  cases found : authority.read request.operation with
  | none => simp [resolve, found] at accepted
  | some source =>
    simp only [resolve, found, bind, Option.bind] at accepted
    split at accepted
    · rename_i matched
      have same := (Option.some.inj accepted).symm
      rw [same, matched.1]
      exact ⟨congrArg authority.digest matched.2.1.symm,
        congrArg authority.digest matched.2.2.1.symm⟩
    · contradiction

theorem realized_symbol_and_sources
    (receipt : Invocation realizationContract prepareRealization (authority, request, symbol)) :
    receipt.result.symbol = symbol ∧ receipt.result.native = request.identity ∧
    receipt.result.intentSource = request.intentSource ∧
    receipt.result.outcomeSource = request.outcomeSource ∧
    symbol.matches request.identity request.symbolic := by
  have accepted := receipt.logic
  change realize authority request symbol = some receipt.result at accepted
  cases checked : resolve authority request with
  | none => simp [realize, checked] at accepted
  | some native =>
    simp only [realize, checked, bind, Option.bind, Realization.select] at accepted
    split at accepted
    · rename_i scopeMatch
      have same := (Option.some.inj accepted).symm
      rw [same]
      exact ⟨rfl, resolved_identity checked, rfl, rfl, by simpa [resolved_identity checked] using scopeMatch⟩
    · contradiction

theorem realized_source_digests
    (receipt : Invocation realizationContract prepareRealization (authority, request, symbol)) :
    receipt.result.native.intentDigest = authority.digest receipt.result.intentSource ∧
    receipt.result.native.outcomeDigest = authority.digest receipt.result.outcomeSource := by
  have accepted := receipt.logic
  change realize authority request symbol = some receipt.result at accepted
  cases checked : resolve authority request with
  | none => simp [realize, checked] at accepted
  | some native =>
    have source := realized_symbol_and_sources receipt
    rw [source.2.1, source.2.2.1, source.2.2.2.1]
    simpa [resolved_identity checked] using resolved_source_digests checked

theorem realization_scope_mismatch (wrong : ¬ symbol.matches request.identity request.symbolic) :
    realize authority request symbol = none := by
  cases checked : resolve authority request with
  | none => simp [realize, checked]
  | some native => simp [realize, checked, Realization.select, resolved_identity checked, wrong]

theorem realization_wrong_operation (wrong : symbol.operation ≠ request.identity.operation) :
    realize authority request symbol = none :=
  realization_scope_mismatch (fun scopeMatch => wrong scopeMatch.2.1)

theorem realization_foreign_receiver (wrong : symbol.receiver ≠ request.identity.receiver) :
    realize authority request symbol = none :=
  realization_scope_mismatch (fun scopeMatch => wrong scopeMatch.2.2.1)

theorem realization_foreign_provider (wrong : symbol.providerKey ≠ request.identity.providerKey) :
    realize authority request symbol = none :=
  realization_scope_mismatch (fun scopeMatch => wrong scopeMatch.2.2.2.1)

theorem realization_foreign_witness (wrong : symbol.witnessKey ≠ request.identity.witnessKey) :
    realize authority request symbol = none :=
  realization_scope_mismatch (fun scopeMatch => wrong scopeMatch.2.2.2.2.1)

theorem realization_wrong_receipt (wrong : symbol.receipt ≠ request.symbolic) :
    realize authority request symbol = none :=
  realization_scope_mismatch (fun scopeMatch => wrong scopeMatch.1)

theorem realization_check_exact (accepted : Realization.check expected candidate = some native) :
    candidate = expected := by
  unfold Realization.check at accepted
  split at accepted
  · assumption
  · contradiction

theorem realization_check_idempotent (expected : Realization) :
    expected.check expected = some expected.native := by simp [Realization.check]

theorem realization_check_rejects_replacement (expected candidate : Realization)
    (different : candidate ≠ expected) :
    expected.check candidate = none := by simp [Realization.check, different]

/-- Recovery cannot reselect a symbolic receipt from a different settled operation. -/
def Authority.forImage (authority : Authority) (image : Revocation.Crash.Image) : Authority :=
  { authority with read := fun operation =>
      (authority.read operation).filter (fun source => decide (image.settledOutcome operation = some source.symbolic)) }

theorem mapping_survives_recovery (authority : Authority) (request : Request) (history : Receiver.LegacyRecoveryTrace initial after) :
    resolve (authority.forImage after) request = resolve (authority.forImage initial) request := by
  have preserved := (Receiver.legacyRecoveryTrace_preserves_effect_state history).2
  simp only [resolve, Authority.forImage, Revocation.Crash.Image.settledOutcome, preserved]
  rfl

end CedarPooSpec.Gateway.OAuth.ReceiptIdentity
