import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Delegation.AgentDelegation

/-!
Per-call value authorization for an AI agent's payment tool request. The
amount, account, and originating user are checked on each proposed call.
-/

namespace CedarPooSpec.AgentPaymentExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.AgentDelegationExample

def accountType : EntityType := ⟨"Account", []⟩
def accountGroupType : EntityType := ⟨"AccountGroup", []⟩
def financeBot : EntityUID := ⟨agentType, "finance-bot"⟩
def paymentTool : EntityUID := ⟨toolType, "process-payment"⟩
def approvedGroup : EntityUID := ⟨accountGroupType, "Approved"⟩
def externalGroup : EntityUID := ⟨accountGroupType, "External"⟩
def approvedAccount : EntityUID := ⟨accountType, "approved"⟩
def reserveAccount : EntityUID := ⟨accountType, "reserve"⟩
def externalAccount : EntityUID := ⟨accountType, "external"⟩
def transfer : EntityUID := ⟨actionType, "transfer"⟩

def paymentEntities : Entities := Map.make (entities.toList ++ [
  (financeBot, agentData 4 "payments" "production" ["process_payment"]),
  (paymentTool, emptyData),
  (approvedGroup, emptyData), (externalGroup, emptyData),
  (approvedAccount, { emptyData with ancestors := Set.make [approvedGroup] }),
  (reserveAccount, { emptyData with ancestors := Set.make [approvedGroup] }),
  (externalAccount, { emptyData with ancestors := Set.make [externalGroup] }),
  (transfer, emptyData)])

def accountEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [accountGroupType], Map.empty, none⟩
def paymentActionEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [accountType], Set.empty,
    Map.make [("amount", .required (.ext .decimal)),
      ("origin", .required (.entity userType))]⟩
def paymentSchema : Schema :=
  ⟨Map.make (schema.ets.toList ++ [
      (accountType, accountEntry), (accountGroupType, emptyEntry)]),
    Map.make (schema.acts.toList ++ [(transfer, paymentActionEntry)])⟩

def decimal (text : String) : Cedar.Spec.Ext.Decimal :=
  match Cedar.Spec.Ext.Decimal.decimal text with
  | some value => value
  | none => panic! s!"invalid transfer amount: {text}"

def amount : Expr := ctx "amount"
def positive : Expr :=
  .call .greaterThan [amount, .call .decimal [.lit (.string "0.0000")]]
def withinCeiling : Expr :=
  .call .lessThanOrEqual [amount, .call .decimal [.lit (.string "100.0000")]]
def originAuthorized : Expr :=
  .and (.binaryApp .mem (ctx "origin") (.lit (.entityUID adminRole)))
    (.getAttr (ctx "origin") "mfa")

def financeToolPolicy : Policy :=
  policy "finance-agent-tool" invoke (.eq financeBot) (.eq paymentTool)
    (.and (.binaryApp .lessEq (.lit (.int 3)) (principalFact "trust"))
      (.and (eq (principalFact "namespace") (.lit (.string "payments")))
        (eq (principalFact "stage") (.lit (.string "production")))))

def paymentBase : Policy :=
  policy "agent-payment" transfer (.eq financeBot) .any (.lit (.bool true))
def veto (id : String) (invalid : Expr) : Policy :=
  { id, effect := .forbid,
    principalScope := paymentBase.principalScope,
    actionScope := paymentBase.actionScope,
    resourceScope := paymentBase.resourceScope,
    condition := [{ kind := .when, body := invalid }] }
def accountVeto : Policy :=
  veto "unapproved-account"
    (.unaryApp .not (.binaryApp .mem (.var .resource) (.lit (.entityUID approvedGroup))))
def amountVeto : Policy :=
  veto "invalid-payment-amount" (.unaryApp .not (.and positive withinCeiling))
def originVeto : Policy :=
  veto "unapproved-payment-origin" (.unaryApp .not originAuthorized)
def frozenAccountVeto : Policy :=
  veto "frozen-payment-account"
    (eq (.var .resource) (.lit (.entityUID approvedAccount)))

def paymentModelResult : Except LeanPoo.C4.Error Model := do
  let tool ← model.mix "FinanceTool" [] [.extend financeToolPolicy]
  let base ← tool.mix "PaymentBase" [] [.extend paymentBase]
  let account ← base.extend "PaymentAccount" "PaymentBase" [.extend accountVeto]
  let amount ← account.extend "PaymentAmount" "PaymentBase" [.extend amountVeto]
  let origin ← amount.extend "PaymentOrigin" "PaymentBase" [.extend originVeto]
  let governed ← origin.mix "PaymentGoverned"
    ["PaymentAccount", "PaymentAmount", "PaymentOrigin"]
  let frozen ← governed.extend "PaymentFrozen" "PaymentGoverned"
    [.extend frozenAccountVeto]
  frozen.extend "PaymentRestored" "PaymentFrozen"
    [.remove frozenAccountVeto.id]

def paymentModel : Model := paymentModelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def paymentProgram : CedarPooSpec.Functional.Program paymentModel paymentSchema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    paymentModel paymentSchema (paymentModel.modules.map (·.name)) (by native_decide)

/-- Inspect the compiled C4 slot at a revision boundary. `some none` is the
    explicit removal tombstone; Cedar publication still validates edit intent. -/
def policySlot (root : String) (id : PolicyID) : Option (Option Policy) :=
  (paymentModel.compilePlan root).toOption.bind fun plan =>
    plan.resolve id (fun _ => none)

/-- The same policy ID is absent, added by freeze, then explicitly removed. -/
def freezeSlotEvolution : List (Option (Option Policy)) :=
  ["PaymentGoverned", "PaymentFrozen", "PaymentRestored"].map fun root =>
    policySlot root frozenAccountVeto.id

def paymentRequest (account origin : EntityUID) (requested : String) : Request :=
  ⟨financeBot, transfer, account, Map.make [
    ("amount", .ext (.decimal (decimal requested))),
    ("origin", .prim (.entityUID origin))]⟩

def checks (root : String) (account origin : EntityUID) (requested : String) :
    List (String × Request) := [
  ("FinanceTool", requestTool financeBot paymentTool),
  (root, paymentRequest account origin requested)]

def authorizePayment
     (root : String) (account origin : EntityUID)
    (requested : String)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Bool :=
  match programContext.authorizeLayers
      (checks root account origin requested) paymentEntities with
  | .error _ => false
  | .ok receipts => CedarPooSpec.Authorization.Compound.layersAllowed receipts

def cases : List (String × String × EntityUID × EntityUID × String × Bool) := [
  ("base-external-high-support", "PaymentBase", externalAccount, support, "500.0000", true),
  ("account-external", "PaymentAccount", externalAccount, admin, "50.0000", false),
  ("account-high", "PaymentAccount", approvedAccount, admin, "500.0000", true),
  ("amount-high", "PaymentAmount", approvedAccount, admin, "100.0001", false),
  ("amount-support", "PaymentAmount", approvedAccount, support, "50.0000", true),
  ("origin-external", "PaymentOrigin", externalAccount, admin, "50.0000", true),
  ("origin-support", "PaymentOrigin", approvedAccount, support, "50.0000", false),
  ("governed-exact-ceiling", "PaymentGoverned", approvedAccount, admin, "100.0000", true),
  ("governed-over-ceiling", "PaymentGoverned", approvedAccount, admin, "100.0001", false),
  ("governed-zero", "PaymentGoverned", approvedAccount, admin, "0.0000", false),
  ("governed-external", "PaymentGoverned", externalAccount, admin, "50.0000", false),
  ("governed-support", "PaymentGoverned", approvedAccount, support, "50.0000", false),
  ("governed-no-mfa", "PaymentGoverned", approvedAccount, adminNoMfa, "50.0000", false),
  ("frozen-target", "PaymentFrozen", approvedAccount, admin, "50.0000", false),
  ("frozen-reserve-unaffected", "PaymentFrozen", reserveAccount, admin, "50.0000", true),
  ("restored-target", "PaymentRestored", approvedAccount, admin, "50.0000", true)]

def casesExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Bool := cases.all fun (_, root, account, origin, requested, expected) =>
  (authorizePayment (programContext := programContext)) root account origin requested == expected

theorem casesExactFully : casesExact = true := by native_decide

def branchesNeedComposition
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Bool :=
  (authorizePayment (programContext := programContext)) "PaymentAccount" approvedAccount support "500.0000" &&
  (authorizePayment (programContext := programContext)) "PaymentAmount" externalAccount admin "50.0000" &&
  (authorizePayment (programContext := programContext)) "PaymentOrigin" approvedAccount admin "500.0000" &&
  !(authorizePayment (programContext := programContext)) "PaymentGoverned" approvedAccount support "500.0000" &&
  !(authorizePayment (programContext := programContext)) "PaymentGoverned" externalAccount admin "50.0000"
theorem branchesNeedCompositionFully : branchesNeedComposition = true := by
  native_decide

theorem accountBranchLocal :
    ((paymentModel.compileRevision "PaymentBase" "PaymentAccount").toOption.get
      (by native_decide)).changedPolicyIds = ["unapproved-account"] := by native_decide
theorem amountBranchLocal :
    ((paymentModel.compileRevision "PaymentBase" "PaymentAmount").toOption.get
      (by native_decide)).changedPolicyIds = ["invalid-payment-amount"] := by native_decide
theorem originBranchLocal :
    ((paymentModel.compileRevision "PaymentBase" "PaymentOrigin").toOption.get
      (by native_decide)).changedPolicyIds = ["unapproved-payment-origin"] := by native_decide
def governedPolicyIds : Bool :=
  match paymentModel.compile "PaymentGoverned" with
  | .error _ => false
  | .ok policies =>
      let ids := policies.map Policy.id
      ids.length == 4 &&
      ["agent-payment", "unapproved-account", "invalid-payment-amount",
        "unapproved-payment-origin"].all ids.contains
theorem governedPolicyIdsFully : governedPolicyIds = true := by native_decide

theorem freezeEditLocal :
    ((paymentModel.compileRevision "PaymentGoverned" "PaymentFrozen").toOption.get
      (by native_decide)).changedPolicyIds = ["frozen-payment-account"] := by native_decide
theorem restoreEditLocal :
    ((paymentModel.compileRevision "PaymentFrozen" "PaymentRestored").toOption.get
      (by native_decide)).changedPolicyIds = ["frozen-payment-account"] := by native_decide
theorem restoredPoliciesEqualGoverned :
    (paymentModel.compile "PaymentRestored" ==
      paymentModel.compile "PaymentGoverned") = true := by native_decide

def malformedOriginRequest : Request :=
  ⟨financeBot, transfer, approvedAccount, Map.make [
    ("amount", .ext (.decimal (decimal "50.0000"))),
    ("origin", .prim (.string "admin"))]⟩
def malformedChecks : List (String × Request) := [
  ("FinanceTool", requestTool financeBot paymentTool),
  ("PaymentGoverned", malformedOriginRequest)]
def malformedOriginRejected
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Bool :=
  match programContext.authorizeLayers malformedChecks paymentEntities with
  | .ok [toolLayer, paymentLayer] =>
      paymentLayer.response.decision == .allow &&
      !paymentLayer.response.erroringPolicies.isEmpty &&
      !CedarPooSpec.Authorization.Compound.layersAllowed [toolLayer, paymentLayer]
  | _ => false
theorem malformedOriginRejectedFully : malformedOriginRejected = true := by
  native_decide

def allRootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Bool :=
  ["FinanceTool", "PaymentBase", "PaymentAccount", "PaymentAmount",
    "PaymentOrigin", "PaymentGoverned", "PaymentFrozen", "PaymentRestored"].all
    fun root => (programContext.publish root).isOk

theorem allRootsValidatedFully : allRootsValidated = true := by native_decide

end CedarPooSpec.AgentPaymentExample
