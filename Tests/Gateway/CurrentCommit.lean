import CedarPooSpec.Vertical.FinancialServices.AgenticCommercePayment
import CedarPooSpec.SchemaJson
import Examples.Enterprise.AWS.FinancialServices.LakehouseGateway.LakehouseGateway
import Examples.Health.MyHealthRecord.ConsumerPlatform

namespace Tests.Gateway.CurrentCommit

open CedarPooSpec CedarPooSpec.Gateway.EffectProtocol
open CedarPooSpec.Gateway.OAuth.Revocation.Crash
open CedarPooSpec.AgenticAI.Commerce CedarPooSpec.Vertical.FinancialServices

def joinedExercise (request : BeginInput) (reserved : Image) : Bool := Id.run do
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
  let .ok hold := currentCommitContract.invoke prepareCurrentCommit current | return false
  let root : Mandate :=
    ⟨"payment-root", ⟨⟨"Account", []⟩, "buyer"⟩, "root-agent", "root-key",
      ["seller"], ["item"], "HKD", 60, 100, 7, 30, true⟩
  let budget : SharedBudget := ⟨root, 14, [], [], 0⟩
  let purchase (state : SharedBudget) (branch operation : String) : SharedBudget.ReservationInput :=
    let child := { root with mandateId := branch, agentId := branch, agentPublicKey := branch, totalCap := 60 }
    let terms : PurchaseTerms := ⟨"seller", "item", branch, branch, 60, "HKD"⟩
    ⟨state, state.revision, [⟨root.agentId, root, child, true⟩], ⟨terms, 25, true⟩,
      ⟨operation, branch, branch, terms⟩⟩
  let proposal := purchase budget "child-a" request.operation
  let input : DelegatedCommitInput :=
    ⟨current, proposal, budget, root :: proposal.steps.map (·.child), proposal.purchase⟩
  let .ok joined := delegatedCommitContract.invoke prepareDelegatedCommit input | return false
  let debited := joined.result.2
  let sibling := purchase debited "child-b" "other-operation"
  let revoked := budget.revoke root.mandateId
  decide (hold.result = reserved ∧ joined.result.1 = reserved ∧ debited.spentMinor = 60) &&
    (currentCommitContract.invoke prepareCurrentCommit { current with actualGeneration := 1 }).isOk == false &&
    (currentCommitContract.invoke prepareCurrentCommit
      { current with independent := reserved, request := { request with
          image := { reserved with retained := request.image.retained } } }).isOk == false &&
    (delegatedCommitContract.invoke prepareDelegatedCommit { input with independentBudget := debited }).isOk == false &&
    (debited.reserve sibling.expectedRevision sibling.steps sibling.offer sibling.purchase).isNone &&
    (delegatedCommitContract.invoke prepareDelegatedCommit
      { input with budget := purchase revoked "child-a" request.operation, independentBudget := revoked }).isOk == false

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
