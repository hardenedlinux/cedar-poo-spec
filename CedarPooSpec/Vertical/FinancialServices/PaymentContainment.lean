import CedarPooSpec.Vertical.FinancialServices.PaymentSigning

/-! A composed, fail-closed wallet containment boundary. The Host must route
all physical signing through this boundary and persist the whole snapshot.
Clearing submission is an observation of a separately authorized recovery
operation, never a payment signing permission or an on-chain implementation. -/
namespace CedarPooSpec.Vertical.FinancialServices.PaymentContainment
open PaymentSigning LeanPoo.Functional.DeclarativeMetadata

structure Snapshot where
  current : PaymentSigning.Current
  exposure : DelegationExposure

/-- Paused or delegated wallets remain quarantined, even for an otherwise valid
native transfer. Wallet/network binding prevents borrowing another wallet's
clean exposure record. The existing signing contract still checks every use. -/
def eligible (state : Snapshot) (request : Request) : Bool :=
  !state.exposure.withdrawalsPaused && !state.exposure.signerRevoked &&
    !state.exposure.clearSubmitted && state.exposure.code.isNone &&
    decide (request.transaction.payer = state.exposure.wallet ∧
      request.transaction.network = state.exposure.network)

def release (state : Snapshot) (request : Request) : Option PaymentSigning.Result :=
  if eligible state request then PaymentSigning.release state.current request else none

/-- One modeled transition couples local suspension to the final-use gateway.
Atomic publication and complete mediation of real endpoints remain Host duties. -/
def pause (state : Snapshot) : Snapshot :=
  { current := { state.current with gateway := { state.current.gateway with revoked := true } },
    exposure := state.exposure.pause }

/-- Refresh independently supplied live facts without reminting the archived
containment state, nonce burns or submitted attempts. Live facts may refresh
clock/audit state but cannot replace the archived journal. Restart must not
replace this boundary with an empty snapshot. -/
def recover (state : Snapshot) (live : PaymentSigning.Current) : Snapshot :=
  { current := { live with
      ledger := { state.current.ledger with
        revision := state.current.ledger.revision + 1
        state := { live.ledger.state with usedNonces := state.current.ledger.state.usedNonces } },
      gateway := { live.gateway with revoked :=
      state.current.gateway.revoked || live.gateway.revoked ||
      state.exposure.withdrawalsPaused || state.exposure.signerRevoked } },
    exposure := state.exposure }

def submitClear (state : Snapshot) : Option Snapshot :=
  if state.exposure.withdrawalsPaused && state.exposure.signerRevoked &&
      state.current.gateway.revoked && state.exposure.code.isSome then
    some { state with exposure := state.exposure.submitClear }
  else none

/-- Exact verified finalized clearing may remove code exposure. It never
resumes withdrawals or restores signing authority automatically. -/
def observeClear (state : Snapshot) (observation : ClearObservation) : Option Snapshot := do
  let exposure ← state.exposure.observeClear observation
  pure { state with exposure }

theorem release_retains_signing (released : release state request = some result) :
    PaymentSigning.release state.current request = some result := by
  unfold release at released
  split at released
  · exact released
  · cases released

theorem release_binds_wallet (released : release state request = some result) :
    request.transaction.payer = state.exposure.wallet ∧
      request.transaction.network = state.exposure.network := by
  unfold release at released
  split at released
  · rename_i admitted
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp admitted).2
  · cases released

theorem paused_cannot_release (paused : state.exposure.withdrawalsPaused = true) :
    release state request = none := by simp [release, eligible, paused]

theorem delegated_cannot_release (installed : state.exposure.code.isSome = true) :
    release state request = none := by
  cases code : state.exposure.code <;> simp_all [release, eligible]

theorem pause_blocks_signing : release (pause state) request = none := by
  simp [release, eligible, pause, DelegationExposure.pause]

theorem pause_preserves_authority : (pause state).exposure.code = state.exposure.code := rfl

theorem recovery_retains_attempts (live : PaymentSigning.Current) :
    (recover state live).current.ledger.attempts = state.current.ledger.attempts := rfl

theorem recovery_retains_burns (live : PaymentSigning.Current) :
    (recover state live).current.ledger.state.usedNonces = state.current.ledger.state.usedNonces := rfl

theorem recovery_retains_pause (live : PaymentSigning.Current) :
    (recover state live).exposure.withdrawalsPaused = state.exposure.withdrawalsPaused := rfl

theorem recovery_cannot_unpause (paused : state.exposure.withdrawalsPaused = true)
    (live : PaymentSigning.Current) : release (recover state live) request = none := by
  exact paused_cannot_release paused

theorem observation_retains_pause (observed : observeClear state observation = some next) :
    next.exposure.withdrawalsPaused = state.exposure.withdrawalsPaused := by
  unfold observeClear at observed
  unfold DelegationExposure.observeClear at observed
  split at observed
  · simp only [pure] at observed
    cases observed
    rfl
  · simp at observed

theorem observation_cannot_resume (paused : state.exposure.withdrawalsPaused = true)
    (observed : observeClear state observation = some next) : release next request = none :=
  paused_cannot_release ((observation_retains_pause observed).trans paused)

/-- Recovery/containment observations are separate from payment requests. -/
inductive Control where
  | pause
  | recover (live : PaymentSigning.Current)
  | submitClear
  | observeClear (observation : ClearObservation)

def step (state : Snapshot) : Control → Snapshot
  | .pause => pause state
  | .recover live => recover state live
  | .submitClear => (submitClear state).getD state
  | .observeClear observation => (observeClear state observation).getD state

def run (state : Snapshot) : List Control → Snapshot
  | [] => state
  | event :: events => run (step state event) events

theorem step_retains_pause (paused : state.exposure.withdrawalsPaused = true)
    (event : Control) : (step state event).exposure.withdrawalsPaused = true := by
  cases event with
  | pause => rfl
  | recover live => exact paused
  | submitClear =>
      simp only [step, submitClear]
      split <;> simpa [DelegationExposure.submitClear] using paused
  | observeClear observation =>
      cases observed : observeClear state observation with
      | none => simpa [step, observed] using paused
      | some next =>
        simpa [step, observed] using (observation_retains_pause observed).trans paused

theorem run_retains_pause (paused : state.exposure.withdrawalsPaused = true)
    (events : List Control) : (run state events).exposure.withdrawalsPaused = true := by
  induction events generalizing state with
  | nil => exact paused
  | cons event events ih => exact ih (step_retains_pause paused event)

theorem no_signing_after_pause (events : List Control) :
    release (run (pause state) events) request = none :=
  paused_cannot_release (run_retains_pause (by rfl) events)

structure Input where
  snapshot : Snapshot
  request : Request

def check (input : Input) : Except String PaymentSigning.Result :=
  match release input.snapshot input.request with
  | some result => .ok result
  | none => .error "wallet containment refused signing"

def contract : Contract Unit Input PaymentSigning.Result where
  input := ⟨"bound-wallet-containment-snapshot", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"contained-current-signing-command", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => check input = .ok result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : Input) : Except String (PaymentSigning.Result × Unit) := do
  let result ← check input
  pure (result, ())

theorem invocation_retains_checks (receipt : Invocation contract prepare input) :
    check input = .ok receipt.result := receipt.logic

end CedarPooSpec.Vertical.FinancialServices.PaymentContainment
