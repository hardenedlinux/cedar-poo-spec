import Examples.Scenarios.FinancialServices.Wallet.Binance2026Host
import CedarPooSpec.Scenarios.Replay

/-! Differential replay of the disclosed chain. Countermodel outputs are
synthetic unchecked signing intents, never real signatures or historical traces.
Settlement uses the existing payment lifecycle; no other chain codec is implied. -/
namespace CedarPooSpec.Binance2026Scenario.Replay
open CedarPooSpec.Vertical.FinancialServices PaymentSigning
open CedarPooSpec.WalletSigningExample CedarPooSpec.Attackers

private def replayMetadata : CedarPooSpec.Scenarios.Metadata :=
  { metadata with
    id := "binance-2026-disclosed-chain-replay",
    title := "Disclosed chain versus mediated wallet effects", kind := .synthetic,
    summary := "Same admitted attacker graph, unsafe mediation countermodel, guarded execution and retained prior exposure",
    disclosures := metadata.disclosures ++ [{
      publisher := "Binance",
      title := "29 October 2026 Binance Security Incident: Initial Findings and Response Update (official mirror)",
      url := "https://www.binance.com/en/square/post/384312159834579",
      publishedOn := "2026-11-03", accessedOn := "2026-11-05", status := .preliminary }],
    limitations := metadata.limitations ++ [
      "Countermodel relay deliberately violates complete mediation; it is not Binance implementation evidence",
      "All nonces and the settlement payment are synthetic; multichain amounts are source claims only",
      "No malware, undisclosed AI exploit, real key, blockchain codec or live chain execution"] }

def scenario := (CedarPooSpec.Scenarios.derive CedarPooSpec.Binance2026Scenario.scenario
  replayMetadata (fun inherited => inherited)).toOption.get (by native_decide)

inductive Mode where
  | guarded | bypassCountermodel
  deriving DecidableEq, Repr

/-- Intentionally unsafe application writer. It keeps the same acquisition
model but ignores the signing, mediation and current-use contracts. Only the
existing first reserved payment is reflected in the ledger; other intents are
untracked bypass outputs, not fabricated approved ledger entries. -/
def bypass (world : PaymentHost.State) (candidate : Request) :
    Option (PaymentHost.State × Transaction) :=
  let ledger := ((world.snapshot.current.ledger.dispatch candidate.operation).map Prod.fst).getD
    world.snapshot.current.ledger
  some ({ world with snapshot := { world.snapshot with current :=
    { world.snapshot.current with ledger } } },
    candidate.transaction)

def guarded (world : PaymentHost.State) (candidate : Request) :
    Option (PaymentHost.State × Transaction) := do
  let (next, raw) ← HostBoundary.invoke world { HostBoundary.input world with request := candidate }
  let transaction ← HostBoundary.host.decode raw
  pure (next, transaction)

theorem guarded_returns_expected (called : guarded world candidate = some (next, result)) :
    result = transaction := by
  cases prior : HostBoundary.invoke world { HostBoundary.input world with request := candidate } with
  | none => simp [guarded, prior] at called
  | some pair =>
      rcases pair with ⟨updated, raw⟩
      by_cases same : raw = HostBoundary.bytes
      · simp [guarded, prior, HostBoundary.host, HostBoundary.baseHost, same] at called
        exact called.2.symm
      · simp [guarded, prior, HostBoundary.host, HostBoundary.baseHost, same] at called

def checkedWriter : CheckedWriter Request PaymentHost.State Transaction (fun result => result = transaction) :=
  ⟨guarded, fun _ _ _ _ called => guarded_returns_expected called⟩

def surface : Mode → Surface Capability Request PaymentHost.State Transaction
  | .guarded => scenario.model.2.checkedSurface reachable checkedWriter
  | .bypassCountermodel => scenario.model.2.surface reachable bypass

/-- This fixture's fixed decoder only releases its actual approved transaction.
The generic factory's theorem retains any required predicate supplied by an
application owner; it does not authenticate that owner's physical meaning. -/
theorem guarded_outputs_checked (initial : PaymentHost.State) (actions : List (Action Capability Request)) :
    ∀ output ∈ (CedarPooSpec.Attackers.run (surface .guarded)
      (scenario.model.2.initialState initial) actions).outputs, output = transaction :=
  ProfileObject.checked_outputs scenario.model.2 reachable checkedWriter initial actions

/-- No proof wrapper can certify the unchecked relay for this same requirement. -/
theorem bypass_has_no_checked_writer :
    ¬ ∃ candidate : CheckedWriter Request PaymentHost.State Transaction (fun result => result = transaction),
      candidate.invoke = bypass := by
  rintro ⟨candidate, same⟩
  let wrong : Request := { request with transaction := { transaction with nonce := transaction.nonce + 1 } }
  let ledger := ((HostBoundary.state.snapshot.current.ledger.dispatch wrong.operation).map Prod.fst).getD
    HostBoundary.state.snapshot.current.ledger
  let next : PaymentHost.State := { HostBoundary.state with
    snapshot := { HostBoundary.state.snapshot with current :=
      { HostBoundary.state.snapshot.current with ledger } } }
  have called : bypass HostBoundary.state wrong = some (next, wrong.transaction) := rfl
  rw [← same] at called
  have exactTx := candidate.preserves _ _ _ _ called
  have nonce := congrArg Transaction.nonce exactTx
  exact Nat.ne_of_gt (Nat.lt_succ_self transaction.nonce) nonce


structure State where
  attacker : CedarPooSpec.Attackers.State Capability PaymentHost.State Transaction
  delegatedUses : Nat := 0
  refusedControls : Nat := 0

def clean : State := ⟨scenario.model.2.initialState HostBoundary.state, 0, 0⟩

/-- A third lane begins with an already handed-off payment and independently
observed delegation. It tests containment, not retroactive prevention. -/
def priorExposure : State :=
  { clean with attacker := { clean.attacker with world :=
    { HostBoundary.emitted.next with snapshot :=
      { HostBoundary.emitted.next.snapshot with exposure } } } }

private def withSnapshot (state : State) (snapshot : PaymentContainment.Snapshot) : State :=
  { state with attacker := { state.attacker with world := { state.attacker.world with snapshot } } }
private def refused (state : State) : State := { state with refusedControls := state.refusedControls + 1 }

inductive Event where
  | attack (action : Action Capability Request)
  | confirmDelegation
  | pause
  | delegatedUse
  | settle (evidence : ProcessorEvidence)
  | submitClear
  | observeFixtureClear
  | closeAccess
  | refresh

/-- Environment/control steps are explicit. Fixture confirmation stands for an
independent canonical-chain observation; emission alone never installs code.
No reported transfer is assigned an undisclosed delegation mechanism. -/
def step (mode : Mode) (state : State) : Event → State
  | .attack action => { state with attacker := CedarPooSpec.Attackers.step (surface mode) state.attacker action }
  | .confirmDelegation =>
      match state.attacker.outputs.reverse.find? (fun tx =>
          tx.kind == .delegateCode && tx.delegatedCode.isSome) with
      | none => refused state
      | some tx => withSnapshot state { state.attacker.world.snapshot with exposure :=
          { state.attacker.world.snapshot.exposure with
            code := tx.delegatedCode,
            installedNonce := tx.nonce, clearNonce := tx.nonce + 1 } }
  | .pause => withSnapshot state (PaymentContainment.pause state.attacker.world.snapshot)
  | .delegatedUse =>
      if state.attacker.world.snapshot.exposure.code.isSome then
        { state with delegatedUses := state.delegatedUses + 1 }
      else refused state
  | .settle evidence =>
      match PaymentContainment.observeSettlement state.attacker.world.snapshot evidence with
      | none => refused state
      | some snapshot => withSnapshot state snapshot
  | .submitClear =>
      match PaymentContainment.submitClear state.attacker.world.snapshot with
      | none => refused state
      | some snapshot => withSnapshot state snapshot
  | .observeFixtureClear =>
      let observed := state.attacker.world.snapshot.exposure
      let fixture : ClearObservation := ⟨observed.wallet, observed.network, observed.clearNonce,
        none, true, true⟩
      match PaymentContainment.observeClear state.attacker.world.snapshot fixture with
      | none => refused state
      | some snapshot => withSnapshot state snapshot
  | .closeAccess =>
      let paused := withSnapshot state (PaymentContainment.pause state.attacker.world.snapshot)
      { paused with attacker := { paused.attacker with known := [], world :=
        { paused.attacker.world with writerEpoch := paused.attacker.world.writerEpoch + 1 } } }
  | .refresh =>
      { state with attacker := { state.attacker with
        world := state.attacker.world.refresh current } }

def settlement : ProcessorEvidence :=
  { payment,
    idempotencyKey := payment.nonce, providerReference := "synthetic-chain-observation",
    outcome := .settled, verified := true, settlement := some {
      payerAccount := payment.payerAccount, instrument := payment.instrument,
      beneficiary := payment.beneficiary, amount := payment.amount, asset := payment.asset,
      network := payment.network, chargedFee := "synthetic-fee" } }

private def calls : List Event := [
  .attack (.call deploymentRequest),
  .attack (.call { deploymentRequest with
    operation := "synthetic-untracked-transfer",
    transaction := { transaction with beneficiary := "attacker", nonce := 43 } }),
  .attack (.call { deploymentRequest with
    operation := "synthetic-delegation",
    transaction := { transaction with
      kind := .delegateCode, nonce := 44, delegatedCode := some "synthetic-attacker-delegate" } }),
  .attack (.call request)]

private def probeAfterPause : Event := .attack (.call { deploymentRequest with
  operation := "synthetic-after-pause", transaction := { transaction with nonce := 45 } })

private def described (id title : String) (basis : CedarPooSpec.Scenarios.Replay.Basis)
    (source : Option Nat) (atUTC : Option String) (limitation : String)
    (events : List Event) : CedarPooSpec.Scenarios.Replay.Stage Event :=
  ⟨⟨id, title, basis, source, atUTC, limitation⟩, events⟩

/-- The same events drive every lane. Source claims do not become runtime proof.
The public cross-chain movements are context, not simulated foreign codecs. -/
def stages : List (CedarPooSpec.Scenarios.Replay.Stage Event) := [
  described "foothold" "Compromised engineer endpoint" .assumed none none
    "Initial compromise is supplied; no recruitment or malware execution" [],
  described "ai-pivot" "AI tool to engineers A/C and deployment token" .reported (some 1)
    (some "2026-10-20") "Source supplies a day, not an exact time"
    ((path.take 4).map Event.attack),
  described "signer-route" "Container to signer: reported 17:15–19:56 UTC" .reported (some 1)
    (some "2026-10-29") "Reported 17:15–19:56 window; no exploit implementation"
    ((path.drop 4).map Event.attack),
  described "multichain-report" "Reported XRP, SOL, OP and BTC outflows" .reported (some 1)
    none "Source-only multichain coverage; no XRP/Solana/Bitcoin or token codec" [],
  described "signing-probes" "Transfer substitution and delegation requests" .probe none none
    "Synthetic requests/nonces; unsafe writer is an explicit countermodel" calls,
  described "delegation-observed" "Independent delegation installation observation" .probe none none
    "Conditional simulated confirmation, not EVM execution or signature verification" [.confirmDelegation],
  described "pause" "Suspend withdrawals and revoke local signer use" .reported (some 1)
    none "Modeled responder action; local pause cannot undo prior signed authority" [.pause],
  described "after-pause" "Probe new signing and existing delegated authority" .probe none none
    "Possibility test; not a claim Binance issued new signatures after suspension"
    [probeAfterPause, .delegatedUse],
  described "late-settlement" "Previously broadcast transfer finalizes" .reported (some 1)
    (some "2026-10-29T23:56:00Z") "Existing payment-lifecycle analogue; not the historical ETH transaction"
    [.settle settlement],
  described "clear-submitted" "Submit separately authorized delegation clearing" .reported (some 1)
    (some "2026-10-30T00:10:00Z") "Synthetic nonce; no clearing signature or transaction submission" [.submitClear],
  described "clear-observed" "Exact verified final clearing observation" .probe none none
    "Independent chain/finality interpretation is assumed; no historical finality time invented"
    [.observeFixtureClear],
  described "after-clear" "Probe removed delegated authority" .probe none none
    "The sequential model excludes new delegated use after observed clearing" [.delegatedUse],
  described "close-access" "Close access and decommission affected credentials" .reported (some 1)
    none "Supplied responder transition; physical route closure and device rebuild are not proved" [.closeAccess],
  described "restart" "Refresh and retry the original campaign" .probe none none
    "Recovery retains pause, burns and unknown exposure; no automatic resumption"
    (.refresh :: campaign.map Event.attack)]

structure Summary where
  signerReachable : Bool
  signingIntents : Nat
  paused : Bool
  delegated : Bool
  delegatedUses : Nat
  settled : Bool
  refused : Nat
  unknown : Bool
  deriving DecidableEq, Repr

def summarize (state : State) : Summary :=
  { signerReachable := decide (.signerNetwork ∈ state.attacker.known),
    signingIntents := state.attacker.outputs.length,
    paused := state.attacker.world.snapshot.exposure.withdrawalsPaused,
    delegated := state.attacker.world.snapshot.exposure.code.isSome,
    delegatedUses := state.delegatedUses,
    settled := (state.attacker.world.snapshot.current.ledger.attemptFor payment.nonce).any
      (fun attempt => attempt.phase == .settled),
    refused := state.attacker.refused + state.refusedControls, unknown := state.attacker.world.unknown }

def frames (mode : Mode) (initial : State) :=
  CedarPooSpec.Scenarios.Replay.collect (step mode) summarize initial stages

def final (mode : Mode) (initial : State) : State :=
  stages.foldl (fun state stage => stage.events.foldl (step mode) state) initial

/-- Reusing a certified acquisition graph cannot certify an unchecked writer.
The same isolated key remains unreachable in the bypass countermodel. -/
theorem bypass_still_isolates_key (actions : List (Action Capability Request)) :
    Capability.signerCredential ∉ (CedarPooSpec.Attackers.run (surface .bypassCountermodel)
      clean.attacker actions).known :=
  ProfileObject.certified_isolation scenario.model.2 reachable bypass
    HostBoundary.state .signerCredential ((of_decide_eq_true scenario.model.2.retains).2.2.1 .signerCredential (by decide)) actions

end CedarPooSpec.Binance2026Scenario.Replay
