import CedarPooSpec.Attackers.ProfileObject
import CedarPooSpec.Vertical.FinancialServices.PaymentContainment
import Examples.Scenarios.FinancialServices.Wallet.Base

/-! Attacker capabilities and executable traces for the financial case.
This graph encodes the public high-level campaign, not undisclosed exploits.
Its independent workflow and signing roots are explicit separation premises. -/
namespace CedarPooSpec.Binance2026Scenario
open CedarPooSpec.Vertical.FinancialServices PaymentSigning
open CedarPooSpec.WalletSigningExample CedarPooSpec.Attackers

inductive Capability where
  | engineerBEndpoint | internalAI | engineerAEndpoint | engineerCEndpoint
  | deploymentToken | container | signerNetwork | signerCredential | workflowAuthority
  deriving DecidableEq, Repr

def compromiseRules : List (Rule Capability) := [
  ⟨[.engineerBEndpoint], .internalAI⟩,
  ⟨[.internalAI], .engineerAEndpoint⟩,
  ⟨[.internalAI], .engineerCEndpoint⟩,
  ⟨[.engineerAEndpoint], .deploymentToken⟩,
  ⟨[.engineerCEndpoint, .deploymentToken], .container⟩,
  ⟨[.container], .signerNetwork⟩]

structure SigningEvent where
  before : PaymentSigning.Current
  request : PaymentSigning.Request
  result : PaymentSigning.Result

def SigningEvent.safe (event : SigningEvent) : Bool :=
  PaymentSigning.accepts event.before event.request &&
    decide (event.result.transaction = event.request.transaction) &&
    match event.before.ledger.attemptFor event.request.operation with
    | none => false
    | some attempt => decide (event.result.transaction =
        Transaction.forPayment attempt.payment event.before.chainNonce)

def invoke (world : PaymentSigning.Current) (input : PaymentSigning.Request) :
    Option (PaymentSigning.Current × SigningEvent) := do
  let result ← release world input
  pure ({ world with ledger := result.ledger }, ⟨world, input, result⟩)

def baseModel : ProfileObject.Model Capability :=
  ⟨[.engineerBEndpoint], [], [.signerCredential, .workflowAuthority], ["exact-effect"]⟩

def objectFamily := do
  let base ← ProfileObject.define "ExternalAttacker" baseModel
  let endpoints ← ProfileObject.augment base "EndpointAndAI" ⟨[], compromiseRules.take 3, [], ["workload-identity"]⟩
  let deployment ← ProfileObject.derive endpoints "DeploymentPivot" ["ExternalAttacker"] ⟨[], compromiseRules.drop 3, [], ["deployment-isolation"]⟩
  let payment ← ProfileObject.mix deployment "FinancialPaymentAttacker" ["EndpointAndAI", "DeploymentPivot"]
  pure (endpoints, deployment, payment)

def objects := objectFamily.toOption.get (by native_decide)
def endpointSession := (ProfileObject.openSession baseModel objects.1).toOption.get (by native_decide)
def deploymentSession := (ProfileObject.openSession baseModel objects.2.1).toOption.get (by native_decide)
def selectedSession := (ProfileObject.openSession baseModel objects.2.2).toOption.get (by native_decide)

/-- Both independently required sibling parents must survive actual selection. -/
def selectedModel : Option (ProfileObject.Certified baseModel) := do
  let endpoints ← ProfileObject.selectSessions endpointSession selectedSession
  let _ ← ProfileObject.selectSessions deploymentSession selectedSession
  pure endpoints.selectedModel

def model := selectedModel.get (by native_decide)

/-- Reported dates are UTC source claims from the initial report, not an
assertion that undisclosed exploit mechanics have been reproduced. -/
def metadata : CedarPooSpec.Scenarios.Metadata :=
  { id := "binance-2026-10-29", title := "Binance wallet-signing incident",
    domain := "financial-services/payment", summary := "Endpoint and AI-tool compromise through deployment authority to wallet signing and persistent delegation",
    kind := .reportedIncident,
    event := some ⟨"2026-10-29", some "2026-10-30", "UTC"⟩,
    disclosures := [{
      publisher := "Binance", title := "29 October 2026 Binance Security Incident: Initial Findings and Response Update",
      url := "https://www.binance.com/en/blog/community/3229153443759566763",
      publishedOn := "2026-11-03", accessedOn := "2026-11-05", status := .preliminary }],
    limitations := ["Initial report; investigation and independent review remain ongoing",
      "UTC event window includes delegation-clearing containment on 2026-10-30",
      "AI exploit mechanics are undisclosed; prompt injection is not assumed",
      "Synthetic control-flow model; no malware, MPC/HSM or EVM reproduction"] }

def scenario :=
  (CedarPooSpec.Scenarios.derive CedarPooSpec.WalletSigningExample.scenario metadata
    (fun wallet => (wallet, model))).toOption.get (by native_decide)

def reachable (known : List Capability) (input : PaymentSigning.Request) : Bool :=
      decide (.signerNetwork ∈ known) &&
        ((decide (.deploymentToken ∈ known) && decide (input.caller = deployment)) ||
          (decide (.signerCredential ∈ known) && decide (input.caller = signer)))

def surface := model.surface reachable invoke

def foothold : State Capability PaymentSigning.Current SigningEvent :=
  model.initialState current

def path : List (Action Capability PaymentSigning.Request) :=
  [.acquire .internalAI, .acquire .engineerAEndpoint, .acquire .engineerCEndpoint,
    .acquire .deploymentToken, .acquire .container, .acquire .signerNetwork]

def deploymentRequest : PaymentSigning.Request := { request with caller := deployment }

def campaign : List (Action Capability PaymentSigning.Request) := path ++
  [.call deploymentRequest,
    .call { deploymentRequest with transaction := { transaction with beneficiary := "attacker" } },
    .call { deploymentRequest with transaction := { transaction with
      kind := .delegateCode, delegatedCode := some "attacker-delegate" } },
    .call request]

theorem invoke_is_checked (world next : PaymentSigning.Current) (input : PaymentSigning.Request)
    (event : SigningEvent) (invoked : invoke world input = some (next, event)) : event.safe = true := by
  cases released : release world input with
  | none => simp [invoke, released] at invoked
  | some result =>
      simp [invoke, released] at invoked
      rcases invoked with ⟨rfl, rfl⟩
      obtain ⟨attempt, found, exactTx⟩ := release_binds_exact_transaction world input result released
      have inputTx := (release_returns_requested_transaction world input result released).symm.trans exactTx
      simp [SigningEvent.safe, release_requires_current_checks world input result released,
        release_returns_requested_transaction world input result released, found, inputTx]

/-- Isolation is derived from the actual inherited/certified model. The base
requires these roots; no duplicated hand-maintained graph proof is needed. -/
theorem model_retains_isolated (cap : Capability) (member : cap ∈ baseModel.isolated) :
    cap ∈ model.model.isolated :=
  (of_decide_eq_true model.retains).2.2.1 cap member

theorem signing_root_unreachable (actions : List (Action Capability PaymentSigning.Request)) :
    Capability.signerCredential ∉ (run surface foothold actions).known :=
  ProfileObject.certified_isolation model reachable invoke current .signerCredential
    (model_retains_isolated _ (by decide)) actions

theorem workflow_root_unreachable (actions : List (Action Capability PaymentSigning.Request)) :
    Capability.workflowAuthority ∉ (run surface foothold actions).known :=
  ProfileObject.certified_isolation model reachable invoke current .workflowAuthority
    (model_retains_isolated _ (by decide)) actions

theorem attacker_outputs_are_checked (actions : List (Action Capability PaymentSigning.Request)) :
    ∀ event ∈ (run surface foothold actions).outputs, event.safe = true :=
  run_preserves_outputs surface (fun event => event.safe = true) (fun world input next event observed => invoke_is_checked world next input event observed) foothold
    (by simp [foothold, ProfileObject.Certified.initialState]) actions

namespace Containment
open CedarPooSpec.Vertical.FinancialServices

def clean : PaymentContainment.Snapshot :=
  ⟨scenario.model.1.1, { exposure with code := none }⟩
def exposed : PaymentContainment.Snapshot := ⟨scenario.model.1.1, exposure⟩
def paused := PaymentContainment.pause exposed
def submitted := (PaymentContainment.submitClear paused).get (by native_decide)
def cleared := (PaymentContainment.observeClear submitted clearObservation).get (by native_decide)
def recovered := PaymentContainment.recover cleared scenario.model.1.1

/-- Reuse the admitted object family's application surface with the stricter
composed writer. A successful dispatch retains exposure and advances the actual
existing ledger; no second payment or attacker model is introduced. -/
def invoke (world : PaymentContainment.Snapshot) (input : PaymentSigning.Request) :
    Option (PaymentContainment.Snapshot × SigningEvent) := do
  let result ← PaymentContainment.release world input
  pure ({ world with current := { world.current with ledger := result.ledger } },
    ⟨world.current, input, result⟩)

def surface := model.surface reachable invoke

def foothold : State Capability PaymentContainment.Snapshot SigningEvent := model.initialState clean

structure Observation where
  id : String
  paused : Bool
  delegated : Bool
  revoked : Bool
  signatureReleased : Bool
  deriving Repr

def observe (id : String) (state : PaymentContainment.Snapshot) : Observation :=
  { id, paused := state.exposure.withdrawalsPaused, delegated := state.exposure.code.isSome,
    revoked := state.current.gateway.revoked,
    signatureReleased := (PaymentContainment.release state scenario.model.1.2).isSome }

def observations : List Observation := [observe "exposed" exposed, observe "paused" paused,
  observe "submitted" submitted, observe "cleared" cleared, observe "recovered" recovered]

end Containment

/-- Actual prefixes of the same admitted POO graph; no second acquisition graph.
The initial compromised endpoint is an assumption, not a simulated infection. -/
structure ReplayStage where
  id : String
  reportedOn : Option String
  reached : Bool
  signerReachable : Bool
  signatures : Nat
  refused : Nat
  deriving Repr

private def replayStage (id : String) (reportedOn : Option String) (actions : List (Action Capability PaymentSigning.Request))
    (goal : Capability) : ReplayStage :=
  let observed := CedarPooSpec.Attackers.run Containment.surface Containment.foothold actions
  { id, reportedOn, reached := decide (goal ∈ observed.known),
    signerReachable := reachable observed.known deploymentRequest,
    signatures := observed.outputs.length, refused := observed.refused }

def replayStages : List ReplayStage := [
  replayStage "endpoint" none [] .engineerBEndpoint,
  replayStage "ai-token" (some "2026-10-20") (path.take 4) .deploymentToken,
  replayStage "deployment" (some "2026-10-29") (path.take 5) .container,
  replayStage "signer" (some "2026-10-29") (path ++ [.call deploymentRequest]) .signerNetwork]



end CedarPooSpec.Binance2026Scenario
