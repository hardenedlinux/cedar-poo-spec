import CedarPooSpec.Vertical.FinancialServices.PaymentContainment
import CedarPooSpec.Gateway.PublicationReview

/-! Pure Host adapter protocol, not a signer or storage implementation. The
independently installed interpretation owns decoders, registrar/source readers
and durable-ack verification. No incoming input supplies those functions.
Exact journals avoid assuming a digest or serialization is injective. -/
namespace CedarPooSpec.Vertical.FinancialServices.PaymentHost
open PaymentSigning CedarPooSpec.Gateway CedarPooSpec.ZeroTrust
open LeanPoo.Functional.DeclarativeMetadata

abbrev Bytes := List Nat
abbrev Credential := PublicationReview.RegistrarBinding String String String String String

structure Cut where
  world : String
  effect : EffectProtocol.EffectIdentity
  review : EffectProtocol.ReviewBinding
  signer : Workload
  nonce : Nat
  writerEpoch : Nat
  deriving DecidableEq

structure Command where
  bytes : Bytes
  transaction : Transaction
  operation : String
  cut : Cut
  deriving DecidableEq

structure Journal where
  ledger : PaymentLedger
  exposure : DelegationExposure
  revoked : Bool
  writerEpoch : Nat
  pending : Option Command
  unknown : Bool
  deriving DecidableEq

structure State where
  snapshot : PaymentContainment.Snapshot
  writerEpoch : Nat
  pending : Option Command := none
  unknown : Bool := false

def State.cut (state : State) : Cut :=
  ⟨state.snapshot.current.gateway.world, state.snapshot.current.gateway.effect,
    state.snapshot.current.gateway.review, state.snapshot.current.signer,
    state.snapshot.current.chainNonce, state.writerEpoch⟩

def State.journal (state : State) : Journal :=
  ⟨state.snapshot.current.ledger, state.snapshot.exposure,
    state.snapshot.current.gateway.revoked, state.writerEpoch, state.pending, state.unknown⟩

structure Input where
  request : Request
  bytes : Bytes
  credential : Credential
  facts : List (FactBinding String String)

structure Plan where
  before : Journal
  after : Journal
  command : Command
  deriving DecidableEq

/-- The verified storage acknowledgment names the entire planned transition.
Its signature alone is not business approval, chain truth or proof of fsync. -/
structure DurableAck where
  plan : Plan
  serial : String
  deriving DecidableEq

structure Host where
  decode : Bytes → Option Transaction
  registrar : PublicationReview.RegistrarAuthority Bytes State String String String String String
  registrarDecidable : ∀ binding bytes state, Decidable (registrar.admitted binding bytes state)
  source : State → FactAuthority String String
  verifiesAck : DurableAck → Bool

/-- Inventory is owned here, not chosen by the request or an incoming verifier. -/
def requiredFacts : List String := ["workload", "policy", "chain", "clock", "journal"]

def Checks (host : Host) (state : State) (input : Input) : Prop :=
  host.decode input.bytes = some input.request.transaction ∧
  input.bytes ≠ [] ∧ input.bytes.all (fun byte => decide (byte < 256)) = true ∧
  host.registrar.admitted input.credential input.bytes state ∧
  input.credential.subject = input.request.caller.subject ∧
  input.credential.incarnation = input.request.caller.release ∧
  input.credential.epoch = state.writerEpoch ∧
  (host.source state).acceptsAll requiredFacts input.facts = true ∧
  input.facts.all (fun fact => decide (fact.source = state.snapshot.current.gateway.world)) = true ∧
  PaymentContainment.eligible state.snapshot input.request = true ∧
  PaymentSigning.accepts state.snapshot.current input.request = true

instance (host : Host) (state : State) (input : Input) : Decidable (Checks host state input) := by
  letI := host.registrarDecidable input.credential input.bytes state
  unfold Checks
  infer_instance

def prepare (host : Host) (state : State) (input : Input) : Option Plan := do
  if state.pending.isSome || state.unknown then none
  if !(decide (Checks host state input)) then none
  let released ← PaymentContainment.release state.snapshot input.request
  let command : Command := ⟨input.bytes, released.transaction, input.request.operation, state.cut⟩
  pure ⟨state.journal, { state.journal with
    ledger := released.ledger, pending := some command, unknown := true }, command⟩

/-- A genuine durable receipt for another command or journal is insufficient.
Recompute against the current pre-state so stale plans cannot cross a pause,
policy change, writer-epoch change or consumed journal. Native CAS is still IO. -/
def commit (host : Host) (state : State) (input : Input) (plan : Plan)
    (ack : DurableAck) : Option State :=
  if prepare host state input = some plan ∧ ack.plan = plan ∧ host.verifiesAck ack = true then
    some { state with
      snapshot := { state.snapshot with current :=
        { state.snapshot.current with ledger := plan.after.ledger } },
      pending := some plan.command, unknown := true }
  else none

/-- Validate the dispatched journal structurally even if storage signed data
prepared by an unrelated client. There is no second policy evaluator. -/
def Plan.valid (plan : Plan) : Prop :=
  plan.before.pending = none ∧ plan.before.unknown = false ∧
  plan.after = { plan.before with
    ledger := plan.after.ledger, pending := some plan.command, unknown := true } ∧
  (plan.before.ledger.dispatch plan.command.operation).map Prod.fst = some plan.after.ledger

instance (plan : Plan) : Decidable plan.valid := by unfold Plan.valid; infer_instance

def EmissionConditions (host : Host) (state : State) (input : Input)
    (plan : Plan) (ack : DurableAck) : Prop :=
  state.pending = some plan.command ∧ state.journal = plan.after ∧
  plan.valid ∧ ack.plan = plan ∧ host.verifiesAck ack = true ∧
  plan.command = ⟨input.bytes, input.request.transaction, input.request.operation, state.cut⟩ ∧
  Checks host state input

instance (host : Host) (state : State) (input : Input) (plan : Plan) (ack : DurableAck) :
    Decidable (EmissionConditions host state input plan ack) := by unfold EmissionConditions; infer_instance

structure Emission where
  next : State
  bytes : Bytes

/-- Logical handoff to the physical signer. Consume the pending slot before
returning bytes and retain unknown exposure. Atomic persistence of this handoff,
all route mediation and prevention of old-state replay remain Host duties. -/
def emit (host : Host) (state : State) (input : Input) (plan : Plan)
    (ack : DurableAck) : Option Emission :=
  if EmissionConditions host state input plan ack then
    some ⟨{ state with pending := none, unknown := true }, plan.command.bytes⟩
  else none

theorem emission_requires_checks (sent : emit host state input plan ack = some output) :
    EmissionConditions host state input plan ack := by
  unfold emit at sent
  split at sent
  · assumption
  · cases sent

theorem emission_binds_bytes (sent : emit host state input plan ack = some output) :
    host.decode plan.command.bytes = some plan.command.transaction := by
  have checked := emission_requires_checks sent
  rw [checked.2.2.2.2.2.1]
  exact checked.2.2.2.2.2.2.1

theorem emission_returns_exact_bytes (sent : emit host state input plan ack = some output) :
    output.bytes = input.bytes ∧ host.decode output.bytes = some input.request.transaction := by
  have checked := emission_requires_checks sent
  have returned : output.bytes = plan.command.bytes := by
    have same := sent
    simp only [emit, ite_eq_left checked, Option.some.injEq] at same
    exact (congrArg Emission.bytes same).symm
  have bound : plan.command.bytes = input.bytes := congrArg Command.bytes checked.2.2.2.2.2.1
  have same := returned.trans bound
  exact ⟨same, by rw [same]; exact checked.2.2.2.2.2.2.1⟩

theorem emission_requires_durable_plan (sent : emit host state input plan ack = some output) :
    ack.plan = plan ∧ host.verifiesAck ack = true ∧ state.journal = plan.after := by
  have checked := emission_requires_checks sent
  exact ⟨checked.2.2.2.1, checked.2.2.2.2.1, checked.2.1⟩

theorem emission_retains_registrar (sent : emit host state input plan ack = some output) :
    host.registrar.admitted input.credential input.bytes state :=
  (emission_requires_checks sent).2.2.2.2.2.2.2.2.2.1

theorem emission_retains_facts (sent : emit host state input plan ack = some output) :
    (host.source state).acceptsAll requiredFacts input.facts = true :=
  (emission_requires_checks sent).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem no_pending_cannot_emit (empty : state.pending = none) :
    emit host state input plan ack = none := by
  unfold emit
  split
  · rename_i checked
    have pending := checked.1
    rw [empty] at pending
    cases pending
  · rfl

theorem emission_consumes_slot (sent : emit host state input plan ack = some output) :
    output.next.pending = none ∧ output.next.unknown = true := by
  unfold emit at sent
  split at sent
  · cases sent; exact ⟨rfl, rfl⟩
  · cases sent

theorem no_second_emission (sent : emit host state input plan ack = some output) :
    emit host output.next otherInput otherPlan otherAck = none :=
  no_pending_cannot_emit (emission_consumes_slot sent).1

theorem unknown_cannot_prepare (unknown : state.unknown = true) :
    prepare host state input = none := by simp [prepare, unknown]

/-- Add Host obligations to an existing requirement without replacing it. -/
def requirement (host : Host) (original : Requirement Input State) : Requirement Input State :=
  strengthen original (fun input state => Checks host state input)

theorem requirement_preserves_original (host : Host) (original : Requirement Input State) :
    Refines original (requirement host original) := strengthen_refines _ _

def contract (host : Host) (state : State) : Contract Unit Input Plan where
  input := ⟨"independent-host-signing-input", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"exact-durable-signing-plan", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input plan => prepare host state input = some plan
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def invoke (host : Host) (state : State) (input : Input) : Except String (Plan × Unit) :=
  match prepare host state input with
  | none => .error "host signing boundary refused"
  | some plan => .ok (plan, ())

theorem invocation_retains_plan (receipt : Invocation (contract host state) (invoke host state) input) :
    prepare host state input = some receipt.result := receipt.logic

/-- Refresh cannot erase pending/unknown exposure. A changed source cut blocks
handoff until a separate recovery design resolves it; no resend is invented. -/
def State.refresh (state : State) (live : PaymentSigning.Current) : State :=
  { state with snapshot := PaymentContainment.recover state.snapshot live }

theorem refresh_retains_exposure (state : State) (live : PaymentSigning.Current) :
    (state.refresh live).pending = state.pending ∧
      (state.refresh live).unknown = state.unknown := ⟨rfl, rfl⟩

theorem unverified_ack_cannot_emit (unverified : host.verifiesAck ack = false) :
    emit host state input plan ack = none := by
  unfold emit
  split
  · rename_i checked
    have verified := checked.2.2.2.2.1
    rw [unverified] at verified
    cases verified
  · rfl

theorem emission_retains_payment_checks (sent : emit host state input plan ack = some output) :
    PaymentContainment.eligible state.snapshot input.request = true ∧
      PaymentSigning.accepts state.snapshot.current input.request = true := by
  have checked := (emission_requires_checks sent).2.2.2.2.2.2
  exact checked.2.2.2.2.2.2.2.2.2

theorem emission_requires_current_cut (sent : emit host state input plan ack = some output) :
    plan.command.cut = state.cut :=
  congrArg Command.cut (emission_requires_checks sent).2.2.2.2.2.1

end CedarPooSpec.Vertical.FinancialServices.PaymentHost
