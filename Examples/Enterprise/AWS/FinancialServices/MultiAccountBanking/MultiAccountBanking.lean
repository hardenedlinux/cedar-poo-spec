import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Platform.AWS.AgentCore.Gateway
import CedarPooSpec.Vertical.FinancialServices.BankingToolOwner
import CedarPooSpec.Vertical.FinancialServices.BankingToolProfile

/-! Projection of the Gateway Cedar boundary in the AWS multi-account banking
sample. LOB JWT authorization, M2M exchange, IAM, and data access remain outside
this model. The owner-composed policy is an equivalent rewrite over the eighteen
named actions below, not a claim about the sample's deployed policy structure. -/

namespace CedarPooSpec.MultiAccountBankingExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Platform.AWS.AgentCore
open CedarPooSpec.Vertical.FinancialServices

def banker : EntityUID := user "relationship-manager"
def colleague : EntityUID := user "colleague"
def gateway : EntityUID := CedarPooSpec.Platform.AWS.AgentCore.gateway "lobfederation-gateway"
def customer : EntityUID := ⟨actionType, "retail-banking___get_customer"⟩
def accounts : EntityUID := ⟨actionType, "retail-banking___get_accounts"⟩
def balance : EntityUID := ⟨actionType, "retail-banking___get_balance"⟩
def profile : EntityUID := ⟨actionType, "retail-banking___get_profile"⟩
def updateBalance : EntityUID := ⟨actionType, "retail-banking___update_balance"⟩
def deleteCustomer : EntityUID := ⟨actionType, "retail-banking___delete_customer"⟩
def payments : EntityUID := ⟨actionType, "transaction-banking___get_payments"⟩
def transfer : EntityUID := ⟨actionType, "transaction-banking___transfer_funds"⟩
def beneficiaries : EntityUID := ⟨actionType, "transaction-banking___get_beneficiaries"⟩
def schedulePayment : EntityUID := ⟨actionType, "transaction-banking___schedule_payment"⟩
def loans : EntityUID := ⟨actionType, "lending-wealth___get_loans"⟩
def creditScore : EntityUID := ⟨actionType, "lending-wealth___get_credit_score"⟩
def eligibility : EntityUID := ⟨actionType, "lending-wealth___check_eligibility"⟩
def emiDetails : EntityUID := ⟨actionType, "lending-wealth___get_emi_details"⟩
def calculateEmi : EntityUID := ⟨actionType, "lending-wealth___calculate_emi"⟩
def lendingPolicy : EntityUID := ⟨actionType, "lending-wealth___search_lending_policies"⟩
def listTools : EntityUID := ⟨actionType, "tools/list"⟩
def initializeAction : EntityUID := ⟨actionType, "initialize"⟩

def retailTools : List EntityUID :=
  [customer, accounts, balance, profile, updateBalance, deleteCustomer]
def transactionTools : List EntityUID :=
  [payments, transfer, beneficiaries, schedulePayment]
def lendingTools : List EntityUID :=
  [loans, creditScore, eligibility, emiDetails, calculateEmi, lendingPolicy]
def protocolActions : List EntityUID := [listTools, initializeAction]
def namedActions : List EntityUID :=
  retailTools ++ transactionTools ++ lendingTools ++ protocolActions

def actionEntry : ActionSchemaEntry :=
  CedarPooSpec.Platform.AWS.AgentCore.actionEntry Map.empty
def schema : Schema :=
  ⟨Map.make [
    (userType, .standard ⟨Set.empty, Map.empty, none⟩),
    (gatewayType, .standard ⟨Set.empty, Map.empty, none⟩)],
    Map.make (namedActions.map (·, actionEntry))⟩

def emptyData : EntityData := entityData
def entities : Entities := Map.make (
  [(banker, emptyData), (colleague, emptyData), (gateway, emptyData)] ++
    namedActions.map (·, emptyData))
def request (user action : EntityUID) : Request :=
  ⟨user, action, gateway, Map.empty⟩

def permitActions (id : String) (actions : List EntityUID) : Policy :=
  scopedPolicy id .permit gateway (.actionInAny actions)

def retailOwner : BankingToolOwner :=
  { policyId := "retail-owned-tools", principalType := userType,
    gateway, actions := retailTools.filter (· != deleteCustomer) }
def transactionTemplate : BankingToolOwner :=
  { policyId := "transaction-owned-tools", principalType := userType,
    gateway, actions := transactionTools }
def transactionProfile : BankingToolProfile.Object :=
  (BankingToolProfile.define "TransactionTools" transactionTemplate)
    |>.toOption.get (by native_decide)
def pausedTransactionProfile : BankingToolProfile.Object :=
  (BankingToolProfile.onActions transactionProfile "TransferPausedTools"
    (transactionTools.filter (· != transfer))).toOption.get
      (by native_decide)
def resumedTransactionProfile : BankingToolProfile.Object :=
  (BankingToolProfile.onActions pausedTransactionProfile "TransferResumedTools"
    transactionTools).toOption.get (by native_decide)
def transactionOwner : BankingToolOwner :=
  (BankingToolProfile.owner? transactionProfile).get (by native_decide)
def pausedTransactionOwner : BankingToolOwner :=
  (BankingToolProfile.owner? pausedTransactionProfile).get (by native_decide)
def resumedTransactionOwner : BankingToolOwner :=
  (BankingToolProfile.owner? resumedTransactionProfile).get
    (by native_decide)
def lendingOwner : BankingToolOwner :=
  { policyId := "lending-owned-tools", principalType := userType,
    gateway, actions := lendingTools }
def protocolPermit : Policy :=
  permitActions "gateway-protocol" protocolActions
def broadPermit : Policy :=
  { permitActions "sample-broad-permit" namedActions with
    actionScope := .actionScope .any }
def deleteVeto : Policy :=
  scopedPolicy "sample-delete-customer-veto" .forbid gateway
    (.actionScope (.eq deleteCustomer))

/-- The sample's broad grant and delete veto are compared with a POO rewrite
    that assigns all sixteen published tools to independent LOB owners. -/
def modelResult : Except LeanPoo.C4.Error Model := do
  let gateway : Model :=
    { modules := [{ name := "Gateway", edits := [.extend deleteVeto] }] }
  let source ← gateway.extend "SampleBroad" "Gateway" [.extend broadPermit]
  let protocol ← source.extend "Protocol" "Gateway" [.extend protocolPermit]
  let retail ← protocol.extend "Retail" "Gateway" [retailOwner.introduce]
  let transaction ← retail.extend "Transaction" "Gateway" [transactionOwner.introduce]
  let lending ← transaction.extend "Lending" "Gateway" [lendingOwner.introduce]
  let owners ← lending.mix "OwnerCombined" ["Retail", "Transaction", "Lending", "Protocol"]
  let paused ← owners.extend "TransferPaused" "OwnerCombined"
    [pausedTransactionOwner.revise]
  paused.extend "TransferResumed" "TransferPaused" [resumedTransactionOwner.revise]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

def decideAt
     (root : String) (req : Request)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) : Option Decision := do
  let response ← (programContext.response root req entities).toOption
  if response.erroringPolicies.isEmpty then some response.decision else none

def expected (action : EntityUID) : Decision :=
  if action == deleteCustomer then .deny else .allow

theorem sourceNamedDecisions :
    [banker, colleague].all (fun user =>
      namedActions.all (fun action =>
        decideAt "SampleBroad" (request user action) == some (expected action))) = true := by
  native_decide

theorem ownerRewriteNamedDecisions :
    [banker, colleague].all (fun user =>
      namedActions.all (fun action =>
        decideAt "OwnerCombined" (request user action) ==
          decideAt "SampleBroad" (request user action))) = true := by
  native_decide

/-- The source's transfer scenario crosses two LOB tools. Neither owner-local
    branch can authorize the entire sequence; their C4 composition can. -/
theorem transferRequiresBothOwners :
    decideAt "Retail" (request banker updateBalance) = some .allow ∧
    decideAt "Retail" (request banker transfer) = some .deny ∧
    decideAt "Transaction" (request banker updateBalance) = some .deny ∧
    decideAt "Transaction" (request banker transfer) = some .allow ∧
    decideAt "OwnerCombined" (request banker updateBalance) = some .allow ∧
    decideAt "OwnerCombined" (request banker transfer) = some .allow := by
  native_decide

theorem lendingNeedsItsOwner :
    decideAt "Retail" (request banker creditScore) = some .deny ∧
    decideAt "OwnerCombined" (request banker creditScore) = some .allow ∧
    decideAt "OwnerCombined" (request banker lendingPolicy) = some .allow := by
  native_decide

theorem transferOverlayIsLocal :
    decideAt "TransferPaused" (request banker transfer) = some .deny ∧
    decideAt "TransferPaused" (request banker balance) = some .allow ∧
    decideAt "TransferPaused" (request banker payments) = some .allow ∧
    decideAt "TransferResumed" (request banker transfer) = some .allow := by
  native_decide

/-- The override invalidates exactly one owner policy body. All other
    Gateway policy bodies are candidates for reuse by revision consumers. -/
theorem pausedRevisionTouchesOnlyTransaction :
    ((model.compileRevision "OwnerCombined" "TransferPaused").toOption.get
      (by native_decide)).changedPolicyIds = [transactionOwner.policyId] := by
  native_decide

theorem allRootsValidated :
    ["Gateway", "SampleBroad", "Protocol", "Retail", "Transaction", "Lending",
      "OwnerCombined", "TransferPaused", "TransferResumed"].all (fun root =>
        (CedarPooSpec.MultiAccountBankingExample.program.publish root).isOk) = true := by
  native_decide

end CedarPooSpec.MultiAccountBankingExample
