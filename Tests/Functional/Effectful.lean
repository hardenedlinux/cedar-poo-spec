import CedarPooSpec.Functional.Admission
import Examples.Health.AgenticAI.LanguageModel.DisclosureExport
import Examples.Enterprise.Agent.Fanout.CrossAgentEgressValidatedExport
import Examples.Enterprise.Personnel.ValidatedExport
import Tests.Language.SchemaProjection
import Tests.Functional.Capabilities

/-! Pre-C2 algorithms remain independent test references. Production consumers
use checked selected operations and retain their actual domain admission gates. -/

namespace CedarPooSpec.EffectfulCapabilitiesTest.Reference.Cross
open CedarPooSpec.CrossAgentEgressExample CedarPooSpec.PolicyModules Cedar.Spec

def authorized (root : String) (view : LedgerView) (state : State)
    (attempt : Attempt) : Bool :=
  match model.compile root with
  | .error _ => false
  | .ok policies => authorizedBy policies view state attempt


def admit (root : String) (view : LedgerView) (state : State)
    (attempt : Attempt) : Bool × State :=
  let allowed := authorized root view state attempt
  let next := advance state attempt
  (allowed, if allowed then { next with epoch := state.epoch + 1 } else state)


def prepare (activeModel : Model) (root : String) (view : LedgerView) (state : State)
    (grantId : String) (effect : BoundEffect) : Option AdmissionTicket :=
  match CedarPooSpec.Admission.PolicySnapshot.capture activeModel root with
  | .error _ => none
  | .ok snapshot =>
      if authorizedBy snapshot.policies view state effect.attempt &&
          (state.authority.check grantId effect).isOk &&
          state.operations.check effect.operationId then
        some ⟨snapshot, view, state.epoch, grantId, effect⟩
      else none

/-- A compare-and-swap admission contract. A real host must persist the
    ledger and execute this check and reservation atomically. -/
def commit (activeModel : Model) (root : String) (view : LedgerView) (state : State)
    (ticket : AdmissionTicket) (effect : BoundEffect) : Option State :=
  if ticket.policy.root != root || ticket.view != view ||
      ticket.epoch != state.epoch || ticket.effect != effect then none
  else
    match ticket.policy.currentPolicies activeModel with
    | .error _ => none
    | .ok policies =>
        if !authorizedBy policies view state effect.attempt ||
            !state.operations.check effect.operationId then none
        else
          match state.authority.consume ticket.grantId effect with
          | .error _ => none
          | .ok authority =>
              match state.operations.admit effect.operationId with
              | none => none
              | some operations =>
                  let next := advance state effect.attempt
                  some { next with authority, operations, epoch := state.epoch + 1 }

def replay (root : String) (view : LedgerView) (initial : State)
    (attempts : List Attempt) : List (Request × Bool) × State :=
  let (state, rows) := attempts.foldl (fun (state, rows) attempt =>
    let req := request view state attempt
    let (allowed, next) := admit root view state attempt
    (next, rows ++ [(req, allowed)])) (initial, [])
  (rows, state)


end CedarPooSpec.EffectfulCapabilitiesTest.Reference.Cross
namespace CedarPooSpec.EffectfulCapabilitiesTest.Reference.Disclosure
open CedarPooSpec.AgenticAI.LanguageModel.Disclosure
open Cedar.Spec (isAuthorized Request)

def authorized (root : String) (state : State) (effect : Effect) : Bool :=
  match publicationModel.compile root with
  | .error _ => false
  | .ok policies =>
      let answer := isAuthorized (projectedRequest state effect)
        publicationEntities policies
      answer.decision == .allow && answer.erroringPolicies.isEmpty


def prepare (root : DeployableRoot) (state : State) (effect : Effect) : Option Ticket :=
  if effect.channel.isEmpty || !authorized root.name state effect then none
  else some ⟨root, state.epoch, state.approvalRevision, state.delegationRevision,
    state.policyRevision, state.audienceRevision, effect⟩

/-- A finite atomic-state model. A real Host must persist the shared ledger
    and audit before making either channel's external effect visible. -/
def redeem (state : State) (ticket : Ticket) (effect : Effect) : Option State :=
  if ticket.epoch != state.epoch ||
      ticket.approvalRevision != state.approvalRevision ||
      ticket.delegationRevision != state.delegationRevision ||
      ticket.policyRevision != state.policyRevision ||
      ticket.audienceRevision != state.audienceRevision ||
      ticket.effect != effect || !authorized ticket.root.name state effect then none
  else
    match state.cohort.record effect.candidateIds with
    | none => none
    | some cohort =>
        let next := { state with epoch := state.epoch + 1 }
        let next := { next with remaining := state.remaining - 1 }
        let next := { next with cohort }
        let next := { next with audit := state.audit ++ [effect.payloadDigest] }
        some next

def release (root : DeployableRoot) (state : State) (effect : Effect) : Option State := do
  let ticket ← prepare root state effect
  redeem state ticket effect


end CedarPooSpec.EffectfulCapabilitiesTest.Reference.Disclosure

/-! The same synthetic requests and composed policy roots are replayed by
the official Cedar Rust validator and authorizer. -/

namespace CedarPooSpec.EffectfulCapabilitiesTest.Reference.DisclosureExport

open CedarPooSpec.AgenticAI.LanguageModel.Disclosure

def manifest : Except String Lean.Json := do
  let rows ← CedarPooSpec.AgenticAI.LanguageModel.Disclosure.cases.mapM fun (name, root, state, effect, _) =>
    CedarPooSpec.PolicyJson.authorizationCase name root
      publicationModel root (projectedRequest state effect) publicationEntities
  CedarPooSpec.SchemaJson.validatedManifest publicationSchema rows

end CedarPooSpec.EffectfulCapabilitiesTest.Reference.DisclosureExport

namespace CedarPooSpec.EffectfulCapabilitiesTest.Reference.CrossExport

open CedarPooSpec.CrossAgentEgressExample

/-- Export each request with the exact ledger facts seen before admission. -/
def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, root, view, attempts, _) in cases do
    for ((req, _), index) in (CedarPooSpec.EffectfulCapabilitiesTest.Reference.Cross.replay root view {} attempts).1.zipIdx do
      let row ← CedarPooSpec.PolicyJson.authorizationCase
        s!"{name}-step-{index}" root model root req entities
      rows := rows ++ [row]
  CedarPooSpec.SchemaJson.validatedManifest schema rows

end CedarPooSpec.EffectfulCapabilitiesTest.Reference.CrossExport

namespace CedarPooSpec.EffectfulCapabilitiesTest.Reference.CustodyExport

open CedarPooSpec.SourceCustodyExample

open CedarPooSpec.SourceCustodyValidatedExport (scenarios)

def manifest : Except String Lean.Json := do
  let rows ← scenarios.mapM fun (name, root, store, operation) =>
    CedarPooSpec.PolicyJson.authorizationCase name root model root
      operation.request store
  CedarPooSpec.SchemaJson.validatedManifest schema rows

end CedarPooSpec.EffectfulCapabilitiesTest.Reference.CustodyExport
namespace CedarPooSpec.EffectfulCapabilitiesTest
open Cedar.Spec Cedar.Validation CedarPooSpec.Functional

private def wire (result : Except String Lean.Json) : Except String String :=
  result.map Lean.Json.compress

example : wire AgenticAI.LanguageModel.DisclosureExport.manifest =
    wire Reference.DisclosureExport.manifest := by native_decide
example : wire CrossAgentEgressValidatedExport.manifest =
    wire Reference.CrossExport.manifest := by native_decide
example : wire SourceCustodyValidatedExport.manifest =
    wire Reference.CustodyExport.manifest := by native_decide

namespace Cross
open CrossAgentEgressExample

/-- Functional fold preserves request-before-decision and state-step order. -/
theorem replay_order (root : String) (view : LedgerView) (initial : State)
    (attempts : List Attempt) :
    replay root view initial attempts =
      (let (state, rows) := attempts.foldl (fun (state, rows) attempt =>
        let req := request view state attempt
        let (allowed, next) := admit root view state attempt
        (next, rows ++ [(req, allowed)])) (initial, [])
       (rows, state)) := by
  simp only [replay, replayFactory, FunctionalCapabilitiesTest.fold_constants]

example : cases.all (fun (_, root, view, attempts, _) =>
    (replay root view {} attempts) == (Reference.Cross.replay root view {} attempts)) = true := by
  native_decide

-- Compare complete ticket values and resulting authority/budget/operation state.
def prepareParity : Bool :=
  [model, reloadedModel].all fun active =>
    ["Read", "History", "Intent", "CrossAgentGoverned", "CrossAgentIncident",
      "CrossAgentRecovered", "missing"].all fun root =>
      [LedgerView.workerLocal, .delegationShared].all fun view =>
        [ticketState, multiGrantState, { ticketState with epoch := 1 },
          { ticketState with authority := {} }, { ticketState with operations :=
            { admitted := [publicSendA.operationId] } }].all fun state =>
          [("send-a", publicSendA), ("send-b", publicSendB), ("read-a", secretReadA),
            ("approval-one", publicSendA), ("approval-two", independentSendA)].all fun (grant, effect) =>
            prepare active root view state grant effect ==
              Reference.Cross.prepare active root view state grant effect
example : prepareParity = true := by native_decide

def commitParity : Bool :=
  [model, reloadedModel].all fun preparedModel =>
    [model, reloadedModel].all fun activeModel =>
      ["CrossAgentGoverned", "CrossAgentIncident", "CrossAgentRecovered", "missing"].all fun root =>
        [ticketState, multiGrantState].all fun initial =>
          [("send-a", publicSendA), ("send-b", publicSendB), ("read-a", secretReadA),
            ("approval-one", publicSendA)].all fun (grant, effect) =>
            match Reference.Cross.prepare preparedModel "CrossAgentGoverned"
                .delegationShared initial grant effect with
            | none => true
            | some ticket =>
              [LedgerView.workerLocal, .delegationShared].all fun view =>
                [initial, { initial with epoch := initial.epoch + 1 },
                  { initial with authority := {} }, { initial with operations :=
                    { admitted := [effect.operationId] } },
                  { initial with budget := { initial.budget with sharedUsed := 100 } }].all fun state =>
                    [effect, { effect with payloadDigest := "substituted" }].all fun actual =>
                      commit activeModel root view state ticket actual ==
                        Reference.Cross.commit activeModel root view state ticket actual
example : commitParity = true := by native_decide

-- The admission bridge checks complete policy bodies/order, not just root/IDs.
def baselineSnapshot : Admission.PolicySnapshot :=
  Admission.PolicySnapshot.capture model "CrossAgentGoverned" |>.toOption.get (by native_decide)
example : (program.refreshPolicy baselineSnapshot).isOk = true := by native_decide
example : (program.refreshPolicy
    { baselineSnapshot with policies := baselineSnapshot.policies.reverse }).isOk = false := by
  native_decide
example : (program.refreshPolicy { baselineSnapshot with
    policies := baselineSnapshot.policies.map (fun policy => { policy with condition := [] }) }).isOk = false := by
  native_decide
example : (match (prepareProgram standard reloadedModel schema ["CrossAgentGoverned"]).toOption with
  | none => false
  | some active => match active.refreshPolicy baselineSnapshot with
    | .error .changed => true
    | _ => false) = true := by native_decide

-- Even identical compiled policies must not bypass a newly invalid schema.
example : (match (prepareProgram standard model SchemaProjectionTest.danglingAncestorSchema []).toOption with
  | none => false
  | some active => match active.refreshPolicy baselineSnapshot with
    | .error (.preparation (.context _ (.schema _))) => true
    | _ => false) = true := by native_decide
end Cross

namespace Disclosure
open CedarPooSpec.AgenticAI.LanguageModel.Disclosure

-- Exactly the fields redeem mutates, including the cumulative cohort and audit.
def outcome (result : Option State) :=
  result.map fun state => (state.epoch, state.remaining, state.cohort, state.audit)

example : CedarPooSpec.AgenticAI.LanguageModel.Disclosure.cases.all
    (fun (_, root, state, effect, _) =>
      authorized root state effect == Reference.Disclosure.authorized root state effect) = true := by
  native_decide

example : CedarPooSpec.AgenticAI.LanguageModel.Disclosure.cases.all
    (fun (_, _, state, effect, _) =>
      [DeployableRoot.governed, .incident, .recovered].all fun root =>
        decide (prepare root state effect = Reference.Disclosure.prepare root state effect) &&
        decide (outcome (release root state effect) =
          outcome (Reference.Disclosure.release root state effect))) = true := by native_decide

-- Prepared tickets must be checked against each independently changed current fact.
def changedStates : List State := [initial,
  { initial with epoch := 1 }, { initial with approvalRevision := 1 },
  { initial with delegationRevision := 1 }, { initial with policyRevision := 1 },
  { initial with audienceRevision := 1 }, { initial with now := 100 },
  { initial with remaining := 0 }, { initial with approvals := [] },
  { initial with delegations := [] }, { initial with recipientGrants := [] },
  { initial with trustedSources := [] }, { initial with auditReady := false },
  { initial with currentRecipients := ["substituted-audience"] }]

example : (match Reference.Disclosure.prepare .governed initial workspaceEffect with
  | none => false
  | some ticket => changedStates.all fun state =>
      [workspaceEffect, messageEffect, externalEffect,
        { workspaceEffect with payloadDigest := "substituted" }].all fun effect =>
          decide (outcome (redeem state ticket effect) =
            outcome (Reference.Disclosure.redeem state ticket effect))) = true := by native_decide

example : (match prepare .governed initial workspaceEffect with
  | none => false
  | some ticket => changedStates.tail.all fun state => (redeem state ticket workspaceEffect).isNone) =
    true := by native_decide
end Disclosure

namespace Custody
open SourceCustodyExample
example : SourceCustodyValidatedExport.scenarios.all (fun (_, root, store, operation) =>
    decisionIn root store operation == (match model.compile root with
    | .error _ => false
    | .ok policies =>
      let response := isAuthorized operation.request store policies
      response.decision == .allow && response.erroringPolicies.isEmpty)) = true := by native_decide
example : decisionIn "SmallTeam" separatedEntities normalRead = false ∧
    decisionIn "SmallTeam" entities normalRead = true := by native_decide
end Custody

open Lean in
run_cmd do
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  for declaration in [``CedarPooSpec.Functional.Ready.policySnapshot_compiled,
      ``CedarPooSpec.Functional.Refreshed.compiled,
      ``CedarPooSpec.Functional.Refreshed.allowed_eq] do
    let dependencies ← collectAxioms declaration
    for dependency in dependencies do
      unless allowed.contains dependency.toString do
        throwError "Functional admission axiom boundary changed: {declaration}: {dependency}"
  logInfo "FUNCTIONAL-CEDAR-ADMISSION-AXIOMS-OK three universal snapshot/refresh proofs"

end CedarPooSpec.EffectfulCapabilitiesTest
