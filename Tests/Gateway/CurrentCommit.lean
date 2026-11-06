import CedarPooSpec.Vertical.FinancialServices.AgenticCommercePayment
import CedarPooSpec.SchemaJson
import Examples.Enterprise.AWS.FinancialServices.LakehouseGateway.LakehouseGateway
import Examples.Health.MyHealthRecord.ConsumerPlatform

namespace Tests.Gateway.CurrentCommit

open CedarPooSpec CedarPooSpec.Gateway.EffectProtocol
open CedarPooSpec.Gateway.OAuth.Revocation.Crash
open CedarPooSpec.AgenticAI.Commerce CedarPooSpec.Vertical.FinancialServices

private def purchase (state : SharedBudget) (branch operation : String) : SharedBudget.ReservationInput :=
  let root := state.root
  let child := { root with mandateId := branch, agentId := branch, agentPublicKey := branch, totalCap := 60 }
  let terms : PurchaseTerms := ⟨"seller", "item", branch, branch, 60, "HKD"⟩
  ⟨state, state.revision, [⟨root.agentId, root, child, true⟩], ⟨terms, 25, true⟩,
    ⟨operation, branch, branch, terms⟩⟩

private def paymentInput (request : BeginInput) : DelegatedCommitInput := Id.run do
  let target := request.read.attempt.target
  let effect : EffectIdentity := ⟨request.operation, "checkout", 7, "terms", "schema", target.audience⟩
  let review : ReviewBinding := ⟨"before", "after", "schema", "world", 7, "review"⟩
  let facts : ZeroTrust.FactAuthority String String :=
    ⟨fun field => ⟨"issuer", "subject", target.audience, "world", field, "value", 0, .observed, 0, 20⟩,
      fun _ => true, 14⟩
  let envelope : Envelope := ⟨"world", {}, effect, review, [facts.expected "scope"]⟩
  let actual : Current :=
    ⟨"world", effect, review, facts, ["scope"], true, true, false, true, true, false⟩
  let current : CurrentCommitInput := ⟨0, 0, envelope, actual, true, request.image, target, request⟩
  let root : Mandate :=
    ⟨"payment-root", ⟨⟨"Account", []⟩, "buyer"⟩, "root-agent", "root-key",
      ["seller"], ["item"], "HKD", 60, 100, 7, 30, true⟩
  let budget : SharedBudget := ⟨root, 14, [], [], 0⟩
  let proposal := purchase budget "child-a" request.operation
  return ⟨current, proposal, budget, root :: proposal.steps.map (·.child), proposal.purchase⟩

def joinedExercise (request : BeginInput) (reserved : Image) : Bool := Id.run do
  let input := paymentInput request
  let current := input.effect
  let budget := input.budget.state
  let root := budget.root
  let .ok hold := currentCommitContract.invoke prepareCurrentCommit current | return false
  let .ok joined := delegatedCommitContract.invoke prepareDelegatedCommit input | return false
  let debited := joined.result.2
  let sibling := purchase debited "child-b" "other-operation"
  let revoked := budget.revoke root.mandateId
  let contender := purchase budget "child-b" "other-operation"
  let some otherWinner := budget.reserve contender.expectedRevision contender.steps
    contender.offer contender.purchase | return false
  let afterOther := purchase otherWinner "child-a" request.operation
  -- Both workers start with a larger shared cap, so the loser still fits
  -- after the winner; the revision, rather than the cap, must refuse it.
  let ample := { budget with root := { root with totalCap := 180 } }
  let firstBudget := purchase ample "child-a" request.operation
  let firstInput := { input with budget := firstBudget, independentBudget := ample, authorizedLineage := ample.root :: firstBudget.steps.map (·.child) }
  let .ok firstReceipt := delegatedCommitContract.invoke prepareDelegatedCommit firstInput | return false
  let afterFirst := firstReceipt.result.2
  let otherIntent := { request.intent with operation := "other-operation" }
  let otherEntries := [otherIntent]
  let otherHistory := { request.history with entries := otherEntries, independent := some (Gateway.Lifecycle.WitnessFrontier.observe request.history.logKey otherEntries) }
  let freshSender := match request.read.attempt.sender with
    | .dpop proof => .dpop { proof with proofId := proof.proofId ++ "-second" }
    | .mtls peer => .mtls peer
  let freshAttempt := { request.read.attempt with sender := freshSender }
  let freshRead := { request.read with checked := firstReceipt.result.1.oauth.checkpoint, replica := firstReceipt.result.1.oauth.checkpoint, attempt := freshAttempt }
  let otherRequest := { request with image := firstReceipt.result.1, read := freshRead, operation := "other-operation", intent := otherIntent, history := otherHistory }
  let otherInput := paymentInput otherRequest
  let newBudget := purchase afterFirst "child-b" "other-operation"
  let loserBudget := { newBudget with expectedRevision := ample.revision }
  let staleLoser := { otherInput with budget := loserBudget, independentBudget := afterFirst, authorizedLineage := afterFirst.root :: loserBudget.steps.map (·.child), authorizedPurchase := loserBudget.purchase }
  let freshLoser := { staleLoser with budget := { loserBudget with expectedRevision := afterFirst.revision } }
  if afterFirst.spentMinor + loserBudget.purchase.terms.amountMinor > afterFirst.root.totalCap ||
      (delegatedCommitContract.invoke prepareDelegatedCommit staleLoser).isOk ||
      !(delegatedCommitContract.invoke prepareDelegatedCommit freshLoser).isOk then return false
  -- Two new contenders start from the same post-winner OAuth image and budget.
  let .ok second := delegatedCommitContract.invoke prepareDelegatedCommit freshLoser | return false
  let thirdIntent := { request.intent with operation := "third-operation" }
  let thirdEntries := [thirdIntent]
  let thirdHistory := { request.history with entries := thirdEntries, independent := some (Gateway.Lifecycle.WitnessFrontier.observe request.history.logKey thirdEntries) }
  let thirdSender := match request.read.attempt.sender with
    | .dpop proof => .dpop { proof with proofId := proof.proofId ++ "-third" }
    | .mtls peer => .mtls peer
  let thirdAttempt := { request.read.attempt with sender := thirdSender }
  let thirdInitialRead := { request.read with checked := firstReceipt.result.1.oauth.checkpoint, replica := firstReceipt.result.1.oauth.checkpoint, attempt := thirdAttempt }
  let thirdInitialRequest := { request with image := firstReceipt.result.1, read := thirdInitialRead, operation := "third-operation", intent := thirdIntent, history := thirdHistory }
  let thirdInitialInput := paymentInput thirdInitialRequest
  let thirdPrepared := purchase afterFirst "child-c" "third-operation"
  let thirdInitial := { thirdInitialInput with budget := thirdPrepared, independentBudget := afterFirst, authorizedLineage := afterFirst.root :: thirdPrepared.steps.map (·.child), authorizedPurchase := thirdPrepared.purchase }
  if !(delegatedCommitContract.invoke prepareDelegatedCommit thirdInitial).isOk then return false
  let thirdRead := { request.read with checked := second.result.1.oauth.checkpoint, replica := second.result.1.oauth.checkpoint, attempt := thirdAttempt }
  let thirdRequest := { request with image := second.result.1, read := thirdRead, operation := "third-operation", intent := thirdIntent, history := thirdHistory }
  let thirdInput := paymentInput thirdRequest
  let thirdBudget := purchase second.result.2 "child-c" "third-operation"
  let thirdStaleBudget := { thirdBudget with expectedRevision := thirdPrepared.expectedRevision }
  let third := { thirdInput with budget := thirdStaleBudget, independentBudget := second.result.2, authorizedLineage := second.result.2.root :: thirdStaleBudget.steps.map (·.child), authorizedPurchase := thirdStaleBudget.purchase }
  let thirdCurrent := { third with budget := thirdBudget }
  if (delegatedCommitContract.invoke prepareDelegatedCommit third).isOk ||
      !(delegatedCommitContract.invoke prepareDelegatedCommit thirdCurrent).isOk then return false
  decide (hold.result = reserved ∧ joined.result.1 = reserved ∧ debited.spentMinor = 60) &&
    (currentCommitContract.invoke prepareCurrentCommit { current with actualGeneration := 1 }).isOk == false &&
    (currentCommitContract.invoke prepareCurrentCommit
      { current with independent := reserved, request := { request with
          image := { reserved with retained := request.image.retained } } }).isOk == false &&
    (delegatedCommitContract.invoke prepareDelegatedCommit { input with independentBudget := debited }).isOk == false &&
    (debited.reserve sibling.expectedRevision sibling.steps sibling.offer sibling.purchase).isNone &&
    decide (otherWinner.spentMinor = 60) &&
    (otherWinner.reserve afterOther.expectedRevision afterOther.steps afterOther.offer afterOther.purchase).isNone &&
    (delegatedCommitContract.invoke prepareDelegatedCommit
      { input with budget := purchase revoked "child-a" request.operation, independentBudget := revoked }).isOk == false

open CedarPooSpec.Gateway.OAuth

structure PaymentSnapshot where
  event : String
  worker : String
  writer : Nat
  cut : Nat
  charge : Nat
  receiver_committed : Bool
  status : String
  deriving DecidableEq, Lean.ToJson

structure PaymentCrashPlan where
  boundary : String
  snapshots : List PaymentSnapshot
  deriving Lean.ToJson

private def expected (boundary : CommitBoundary) : PaymentCrashPlan :=
  let committed := match boundary with | .staged => false | .durable => true
  ⟨if committed then "receiver-durable" else "oauth-reserved",
    [⟨"winner-crash", "winner", 0, 0, 60, committed, "unresolved"⟩,
     ⟨"workers-stopped", "both", 0, 0, 60, committed, "unresolved"⟩,
     ⟨"handoff", "a", 1, 1, 60, committed, "unresolved"⟩,
     ⟨"reconcile-stop", "a", 1, 1, 60, committed, if committed then "reconciled" else "unresolved"⟩,
     ⟨"handoff", "b", 2, 2, 60, committed, if committed then "reconciled" else "unresolved"⟩,
     ⟨"reconcile", "b", 2, 2, 60, committed, if committed then "reconciled" else "unresolved"⟩,
     ⟨"stale-restart", "a", 2, 2, 60, committed, if committed then "reconciled" else "unresolved"⟩,
     ⟨"independent-check", "parent", 2, 2, 60, committed, if committed then "reconciled" else "unresolved"⟩]⟩

def paymentCrashPlan : Lean.Json :=
  Lean.toJson [expected .staged, expected .durable]

private def observe (state : Image × SharedBudget) (pin : Receiver.Checkpoint)
    (operation event worker : String) : PaymentSnapshot :=
  ⟨event, worker, state.1.writer, pin.image.cut.generation, state.2.spentMinor,
    (Receiver.evidence pin.image ⟨operation⟩).isSome,
    match effectStatus state.1 operation with
    | .unreserved => "unreserved"
    | .unresolved => "unresolved"
    | .reconciled => "reconciled"⟩

def paymentCrashExercise (managed : Receiver.ManagedInput) (committed : Receiver.ManagedResult)
    (audit : ReconcileInput) (grant : PAR.VerifiedClient Refresh.RefreshDigest)
    (conflict : ProviderOutcome) (boundary : CommitBoundary) : Bool := Id.run do
  let some primary := managed.independent | return false
  let operation := managed.authorization.operation
  let input := paymentInput managed.authorization
  let .ok charged := delegatedCommitContract.invoke prepareDelegatedCommit input | return false
  if charged.result.1 != committed.oauth then return false
  let state := charged.result
  let pin := recoverImage boundary primary committed.receiver
  let recover (state : Image × SharedBudget) (command : DelegatedRecoveryCommand) :=
    delegatedRecoveryContract.invoke prepareDelegatedRecovery ⟨state, command⟩
  let .ok first := recover state (.handoff 0) | return false
  let .ok firstPin := Receiver.promotionContract.invoke Receiver.preparePromotion
    ⟨some pin, pin, pin.image, "standby"⟩ | return false
  let next := firstPin.result
  let firstObservation : Receiver.ManagedReconciliation :=
    ⟨some next, next.active, next.image, { audit with image := first.result.1, writer := 1 }⟩
  let firstAttempt := recover first.result (.reconcile firstObservation)
  let firstRecovered ← match boundary, firstAttempt with
    | .staged, .error _ => pure first.result
    | .durable, .ok settled => pure settled.result
    | _, _ => return false
  let .ok revoked := recover firstRecovered (.revoke 1 grant state.2.root.mandateId) | return false
  let .ok final := recover revoked.result (.handoff 1) | return false
  let .ok finalPin := Receiver.promotionContract.invoke Receiver.preparePromotion
    ⟨some next, next, next.image, "successor"⟩ | return false
  let last := finalPin.result
  let observation : Receiver.ManagedReconciliation :=
    ⟨some last, last.active, last.image, { audit with image := final.result.1, writer := 2 }⟩
  let retryRequest := { managed.authorization with image := final.result.1, writer := 2, checkedWriter := 2 }
  let retryEffect := { input.effect with independent := final.result.1, request := retryRequest }
  let retryBudget := { input.budget with state := final.result.2, expectedRevision := final.result.2.revision }
  let retry := { input with effect := retryEffect, budget := retryBudget, independentBudget := final.result.2 }
  let rejected := recover final.result (.reconcile { observation with audit :=
    { observation.audit with actions := [conflict.receipt.action], outcomes := [conflict] } })
  if rejected.isOk || retry.commit.isSome || (recover final.result (.handoff 1)).isOk then return false
  let outcome := managed.delivery.request.outcome
  let finish := recover final.result (.reconcile observation)
  let recovered ← match boundary, finish with
    | .staged, .error _ => pure final.result
    | .durable, .ok settled =>
      let again := { observation with audit := { observation.audit with image := settled.result.1 } }
      let .ok confirmed := recover settled.result (.reconcile again) | return false
      if confirmed.result != settled.result ||
          settled.result.1.settledOutcome operation != some outcome then return false
      pure settled.result
    | _, _ => return false
  return decide (recovered.2.reservations = state.2.reservations) &&
    decide ([observe state pin operation "winner-crash" "winner",
      observe state pin operation "workers-stopped" "both",
      observe first.result next operation "handoff" "a",
      observe firstRecovered next operation "reconcile-stop" "a",
      observe final.result last operation "handoff" "b",
      observe recovered last operation "reconcile" "b",
      observe recovered last operation "stale-restart" "a",
      observe recovered last operation "independent-check" "parent"] = (expected boundary).snapshots)

def paymentCrashFixture (durable : Revocation.Recovery.Store)
    (read : Revocation.ReplicaRead) (grant : PAR.VerifiedClient Refresh.RefreshDigest) : Bool := Id.run do
  let image : Image := { oauth := durable }
  let intent : CommitRef := ⟨"effect", [1], [2]⟩
  let history : History := ⟨"log", [intent], true,
    some (Gateway.Lifecycle.WitnessFrontier.observe "log" [intent])⟩
  let begin : BeginInput := ⟨image, 0, 0, read, intent.operation, intent, "provider", history, none⟩
  let source : ZeroTrust.FactAuthority String String :=
    ⟨fun field => ⟨"issuer", "subject", "fhir", "source", field, "value", 0, .observed, 0, 20⟩,
      fun _ => true, 14⟩
  let trust : ProviderAuditTrust :=
    ⟨"provider", "log", fun _ outcome => outcome.signature == [7], fun _ _ _ => true⟩
  let action : AuditRecord := ⟨intent.operation, "result"⟩
  let outcome : ProviderOutcome := ⟨{}, "cedar-poo/provider-outcome", "log", ⟨action, intent⟩, [7]⟩
  let receiver : Receiver.Image := { cut := ⟨"receiver", 0⟩ }
  let dispatch : CedarPooSpec.Admission.DispatchBinding := ⟨⟨intent.operation⟩, "effect-digest", receiver.cut⟩
  let delivery : Receiver.Input := ⟨receiver, ⟨dispatch, "channel-one", outcome⟩, dispatch, "channel-one", intent, true⟩
  let primary : Receiver.Checkpoint := ⟨"primary", receiver, none, some durable.checkpoint.authorityId, "receiver-pin"⟩
  let managed : Receiver.ManagedInput := ⟨some primary, "primary", delivery,
    { begin with receiver := some primary.binding }⟩
  let .ok committed := Receiver.managedContract.invoke Receiver.prepareManaged managed | return false
  let audit : ReconcileInput := ⟨image, 0, intent.operation, trust, source, history, [action], [outcome]⟩
  let conflict := { outcome with receipt := ⟨{ action with value := "different" }, intent⟩ }
  return [CommitBoundary.staged, .durable].all
    (paymentCrashExercise managed committed.result audit grant conflict)

private def profile (audience : String) (schema : Cedar.Validation.Schema)
    (case : Lean.Json) : Except String Lean.Json := do
  return Lean.Json.mkObj [("audience", Lean.toJson audience),
    ("schema", ← (SchemaJson.schema schema).mapError reprStr), ("case", case)]

def profiles : Except String Lean.Json := do
  let agent ← LakehouseGatewayExample.program.authorizationCase "agentcore-final-use"
    "agentcore" "FailClosed"
    (LakehouseGatewayExample.request LakehouseGatewayExample.policyholderUS
      LakehouseGatewayExample.queryClaims (some "US")) LakehouseGatewayExample.entities
  let fhir ← MyHealthRecordExample.program.authorizationCase "fhir-final-use" "fhir" "ConsumerPlatform"
    (MyHealthRecordExample.request MyHealthRecordExample.app MyHealthRecordExample.fetch
      MyHealthRecordExample.summaryA) MyHealthRecordExample.entities
  return Lean.toJson [← profile "agentcore" LakehouseGatewayExample.schema agent,
    ← profile "fhir" MyHealthRecordExample.schema fhir]

end Tests.Gateway.CurrentCommit

#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.current_commit_rejects_stale_generation
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.current_commit_rejects_older_image
#print axioms CedarPooSpec.Gateway.OAuth.Revocation.Crash.current_commit_binds_oauth_target
#print axioms CedarPooSpec.Vertical.FinancialServices.delegated_commit_preserves_debits
#print axioms CedarPooSpec.Vertical.FinancialServices.delegated_commit_preserves_prior_hold
#print axioms CedarPooSpec.Vertical.FinancialServices.delegated_commit_refuses_losing_revision
#print axioms CedarPooSpec.Vertical.FinancialServices.delegated_commit_refuses_losing_revision_with_current_oauth

#print axioms CedarPooSpec.Vertical.FinancialServices.delegated_recovery_cannot_reopen_operation
#print axioms CedarPooSpec.Vertical.FinancialServices.delegated_recovery_two_steps_preserve_reservations
#print axioms CedarPooSpec.Vertical.FinancialServices.delegated_recovery_two_steps_cannot_reopen
