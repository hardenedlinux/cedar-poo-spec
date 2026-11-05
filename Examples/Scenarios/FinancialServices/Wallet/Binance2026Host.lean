import Examples.Scenarios.FinancialServices.Wallet.Binance2026
import CedarPooSpec.Vertical.FinancialServices.PaymentHost

/-! Synthetic Host interpretation for the existing Binance Scenario. Tokens,
bytes and receipts below are fixtures, not cryptographic or chain evidence. -/
namespace CedarPooSpec.Binance2026Scenario.HostBoundary
open CedarPooSpec.Vertical.FinancialServices CedarPooSpec.ZeroTrust
open CedarPooSpec.WalletSigningExample PaymentHost

def state : State := ⟨Containment.clean, 7, none, false⟩
def bytes : Bytes := [2, 7, 42]

def credential (state : State) : Credential :=
  ⟨state.snapshot.current.signer.subject, state.snapshot.current.signer.release,
    "registered-signer-key-7", "native-payment", "physical-signer", state.writerEpoch, 7⟩

def expected (state : State) (field : String) : FactBinding String String :=
  { issuer := "independent-host-reader", subject := toString state.snapshot.exposure.wallet,
    audience := state.snapshot.current.signer.subject, source := state.snapshot.current.gateway.world,
    field, value := if field = "workload" then state.snapshot.current.signer.release
      else if field = "policy" then state.snapshot.current.gateway.review.report
      else if field = "chain" then toString state.snapshot.current.chainNonce
      else if field = "journal" then reprStr state.snapshot.current.ledger
      else "independent-clock", generation := state.writerEpoch, origin := .attested,
    notBefore := 1, expiresAt := 25 }

def facts (state : State) := requiredFacts.map (expected state)
def input (state : State) : Input := ⟨request, bytes, credential state, facts state⟩

def baseHost : Host where
  decode := fun raw => if raw = bytes then some transaction else none
  registrar := {
    current := credential
    issued := fun binding actual => binding = credential actual
    roleAllowed := fun subject actual => subject = actual.snapshot.current.signer.subject
    expectedScope := fun _ => "native-payment"
    expectedAudience := fun _ => "physical-signer"
    revoked := fun _ actual => actual.snapshot.current.gateway.revoked = true
    possession := fun _ raw _ => raw = bytes }
  registrarDecidable := fun _ _ _ => by
    unfold CedarPooSpec.Gateway.PublicationReview.RegistrarAuthority.admitted
    dsimp
    infer_instance
  source := fun actual => ⟨expected actual, fun item => decide (item = expected actual item.field), 10⟩
  verifiesAck := fun _ => false

def plan : Plan := (PaymentHost.prepare baseHost state (input state)).get (by native_decide)
def ack : DurableAck := ⟨plan, "fixture-durable-cas-7"⟩
def host : Host := { baseHost with verifiesAck := fun receipt => decide (receipt = ack) }
def committed : State := (PaymentHost.commit host state (input state) plan ack).get (by native_decide)
def emitted : Emission := (PaymentHost.emit host committed (input committed) plan ack).get (by native_decide)

/-- The same admitted Attackers object family supplies acquisition rules.
Only the writer changes: every output crosses the complete Host protocol. -/
def invoke (actual : State) (candidate : Input) : Option (State × Bytes) := do
  let proposed ← PaymentHost.prepare host actual candidate
  let saved ← PaymentHost.commit host actual candidate proposed ack
  let handed ← PaymentHost.emit host saved { candidate with facts := facts saved } proposed ack
  pure (handed.next, handed.bytes)

def surface := model.surface (fun known candidate => reachable known candidate.request) invoke

def foothold : CedarPooSpec.Attackers.State Capability State Bytes := model.initialState state

def campaign : List (CedarPooSpec.Attackers.Action Capability Input) :=
  CedarPooSpec.Binance2026Scenario.campaign.map fun action => match action with
    | .acquire capability => .acquire capability
    | .call request => .call { input state with request }

structure Observation where
  id : String
  admitted : Bool
  deriving Repr

def observations : List Observation := [
  ⟨"exact-handoff", (PaymentHost.emit host committed (input committed) plan ack).isSome⟩,
  ⟨"changed-bytes", (PaymentHost.prepare host state { input state with bytes := [2,7,43] }).isSome⟩,
  ⟨"missing-fact", (PaymentHost.prepare host state { input state with facts := (facts state).drop 1 }).isSome⟩,
  ⟨"stale-writer", (PaymentHost.commit host { state with writerEpoch := 8 }
    (input state) plan ack).isSome⟩,
  ⟨"missing-durable-ack", (PaymentHost.commit host state (input state) plan
    { ack with serial := "invented" }).isSome⟩,
  ⟨"pause-before-handoff", (PaymentHost.emit host
    { committed with snapshot := PaymentContainment.pause committed.snapshot }
    (input committed) plan ack).isSome⟩,
  ⟨"lost-reply-retry", (PaymentHost.emit host emitted.next (input emitted.next) plan ack).isSome⟩]

end CedarPooSpec.Binance2026Scenario.HostBoundary
