import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.Governance.MemberGrant
import CedarPooSpec.Governance.Veto
import CedarPooSpec.Governance.SeparationOfDuties

/-!
A procurement authorization model combining Cedar decimal amounts with
separation of duties. Amount limits, organization, and identities are fictive.
-/

namespace CedarPooSpec.PurchaseApprovalExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Governance

def userType : EntityType := ⟨"User", []⟩
def roleType : EntityType := ⟨"Role", []⟩
def orderType : EntityType := ⟨"PurchaseOrder", []⟩
def groupType : EntityType := ⟨"OrderGroup", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def alice : EntityUID := ⟨userType, "alice"⟩
def bob : EntityUID := ⟨userType, "bob"⟩
def approver : EntityUID := ⟨roleType, "Approver"⟩
def operations : EntityUID := ⟨groupType, "Operations"⟩
def research : EntityUID := ⟨groupType, "Research"⟩
def operationsOrder : EntityUID := ⟨orderType, "ops-1"⟩
def researchOrder : EntityUID := ⟨orderType, "research-1"⟩
def approve : EntityUID := ⟨actionType, "approve"⟩

def decimal (value : String) : Cedar.Spec.Ext.Decimal :=
  match Cedar.Spec.Ext.Decimal.decimal value with
  | some amount => amount
  | none => panic! s!"invalid example amount: {value}"

def orderData (owner group : EntityUID) : EntityData :=
  { attrs := Map.make [
      ("requester", .prim (.entityUID owner)),
      ("limit", .ext (.decimal (decimal "500.0000")))],
    ancestors := Set.make [group], tags := Map.empty }

def emptyData (parents : List EntityUID := []) : EntityData :=
  { attrs := Map.empty, ancestors := Set.make parents, tags := Map.empty }

def entities : Entities := Map.make [
  (alice, emptyData [approver]), (bob, emptyData [approver]),
  (approver, emptyData), (operations, emptyData), (research, emptyData),
  (operationsOrder, orderData alice operations),
  (researchOrder, orderData bob research),
  (approve, emptyData)]

def userEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [roleType], Map.empty, none⟩
def roleEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.empty, none⟩
def orderEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [groupType], Map.make [
    ("requester", .required (.entity userType)),
    ("limit", .required (.ext .decimal))], none⟩
def groupEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.empty, none⟩
def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [userType], Set.make [orderType], Set.empty,
    Map.make [("amount", .required (.ext .decimal))]⟩
def schema : Schema :=
  ⟨Map.make [(userType, userEntry), (roleType, roleEntry),
    (orderType, orderEntry), (groupType, groupEntry)],
    Map.make [(approve, actionEntry)]⟩

def amount : Expr := .getAttr (.var .context) "amount"
def limit : Expr := .getAttr (.var .resource) "limit"
def withinLimit : Expr := .call .lessThanOrEqual [amount, limit]
def positiveAmount : Expr := .call .greaterThan [amount, .call .decimal [.lit (.string "0.0000")]]
def withinBudget : Expr := .and positiveAmount withinLimit
def operationsGrant : MemberGrant :=
  ⟨"operations-approval", approver, .actionScope (.eq approve), operations, []⟩

def legacyPermit : Policy := operationsGrant.policy

def boundedPermit : Policy :=
  { operationsGrant with condition := [{ kind := .when, body := withinBudget }] }.policy

def dutiesControl : SeparationOfDuties :=
  { policyId := "no-self-approval", actionScope := .actionScope (.eq approve),
    priorActorAttribute := "requester",
    principalScope := .principalScope (.mem approver),
    resourceScope := .resourceScope (.is orderType) }
def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [{ name := "Base", edits := [operationsGrant.edit .introduce] }] }
  let budgetEdit := ({ operationsGrant with
    condition := [{ kind := .when, body := withinBudget }] } : MemberGrant).edit .revise
  let budget ← base.extend "Budget" "Base" [budgetEdit]
  let duties ← budget.extend "Duties" "Base" [dutiesControl.edit .introduce]
  duties.mix "Integrated" ["Budget", "Duties"]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

def request (principal resource : EntityUID) (requested : String) : Request :=
  ⟨principal, approve, resource,
    Map.make [("amount", .ext (.decimal (decimal requested)))]⟩

def cases : List (String × String × Request × Decision) := [
  ("base-self-over-limit", "Base", request alice operationsOrder "500.0001", .allow),
  ("budget-self-under-limit", "Budget", request alice operationsOrder "499.9999", .allow),
  ("duties-other-over-limit", "Duties", request bob operationsOrder "500.0001", .allow),
  ("integrated-self-under-limit", "Integrated", request alice operationsOrder "499.9999", .deny),
  ("integrated-other-exact-limit", "Integrated", request bob operationsOrder "500.0000", .allow),
  ("integrated-other-over-limit", "Integrated", request bob operationsOrder "500.0001", .deny),
  ("integrated-other-zero", "Integrated", request bob operationsOrder "0.0000", .deny),
  ("integrated-other-negative", "Integrated", request bob operationsOrder "-1.0000", .deny),
  ("integrated-cross-department", "Integrated", request alice researchOrder "10.0000", .deny)]

def decisionsExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PurchaseApprovalExample.model CedarPooSpec.PurchaseApprovalExample.schema :=
      CedarPooSpec.PurchaseApprovalExample.program) : Bool := cases.all fun (_, root, req, expected) =>
  match programContext.response root req entities with
  | .error _ => false
  | .ok response =>
      response.decision == expected && response.erroringPolicies.isEmpty

theorem decisionsExactFully : decisionsExact = true := by native_decide

theorem budgetEditLocal :
    ((model.compileRevision "Base" "Budget").toOption.get
      (by native_decide)).changedPolicyIds = ["operations-approval"] := by native_decide

theorem validatedPublication :
    (CedarPooSpec.PurchaseApprovalExample.program.publish "Integrated").isOk = true := by
  native_decide

def malformedPermit : Policy :=
  { boundedPermit with condition :=
      [{ kind := .when, body := .lit (.string "not-boolean") }] }
def malformedModel : Model := { modules := model.modules ++ [
  { name := "Malformed", parentOrders := [["Integrated"]],
    edits := [.overlay malformedPermit] }] }

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def malformedProgram : CedarPooSpec.Functional.Program malformedModel schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    malformedModel schema [] (by native_decide)


theorem malformedPublicationRejected :
    (match CedarPooSpec.PurchaseApprovalExample.malformedProgram.publish "Malformed" with
     | .error (.context "Malformed" (.policy _)) => true
     | _ => false) = true := by native_decide

end CedarPooSpec.PurchaseApprovalExample
