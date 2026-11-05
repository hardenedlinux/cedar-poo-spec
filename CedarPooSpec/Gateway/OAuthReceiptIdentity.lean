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
