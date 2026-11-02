import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.PolicyProfile

/-! A proposed Cedar projection of two operations in AWS's agentic platform
expense sample. The source tool currently lists all expenses for listTeamExpenses
and updates a rejection without an AVP call. Base models those observable gaps;
the composed roots are proposed controls, not deployed AWS policies. -/

namespace CedarPooSpec.AWS.Expense

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules

def userType : EntityType := ⟨"User", ["AnyCompany"]⟩
def groupType : EntityType := ⟨"Group", ["AnyCompany"]⟩
def expenseType : EntityType := ⟨"Expense", ["AnyCompany"]⟩
def actionType : EntityType := ⟨"Action", ["AnyCompany"]⟩

def alice : EntityUID := ⟨userType, "alice@company.example"⟩
def bob : EntityUID := ⟨userType, "bob@company.example"⟩
def carol : EntityUID := ⟨userType, "carol@company.example"⟩
def approvers : EntityUID := ⟨groupType, "ExpenseApprovers"⟩
def salesExpense : EntityUID := ⟨expenseType, "sales-pending"⟩
def financeExpense : EntityUID := ⟨expenseType, "finance-pending"⟩
def approvedExpense : EntityUID := ⟨expenseType, "sales-approved"⟩
def listTeam : EntityUID := ⟨actionType, "listTeamExpenses"⟩
def reject : EntityUID := ⟨actionType, "rejectExpense"⟩

def userData (email department : String) (manager : Bool) : EntityData :=
  { attrs := Map.make [
      ("email", .prim (.string email)),
      ("department", .prim (.string department)),
      ("approvalLimit", .prim (.int 500))],
    ancestors := if manager then Set.make [approvers] else Set.empty,
    tags := Map.empty }

def expenseData (submitter department status : String) : EntityData :=
  { attrs := Map.make [
      ("amount", .prim (.int 120)),
      ("submitterEmail", .prim (.string submitter)),
      ("department", .prim (.string department)),
      ("status", .prim (.string status))],
    ancestors := Set.empty, tags := Map.empty }

def emptyData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }

def entities : Entities := Map.make [
  (alice, userData "alice@company.example" "Sales" false),
  (bob, userData "bob@company.example" "Finance" true),
  (carol, userData "carol@company.example" "Sales" true),
  (approvers, emptyData),
  (salesExpense, expenseData "alice@company.example" "Sales" "submitted"),
  (financeExpense, expenseData "bob@company.example" "Finance" "submitted"),
  (approvedExpense, expenseData "alice@company.example" "Sales" "approved"),
  (listTeam, emptyData), (reject, emptyData)]

def userEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [groupType], Map.make [
    ("email", .required .string),
    ("department", .required .string),
    ("approvalLimit", .required .int)], none⟩
def groupEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.empty, none⟩
def expenseEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("amount", .required .int),
    ("submitterEmail", .required .string),
    ("department", .required .string),
    ("status", .required .string)], none⟩
def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [userType], Set.make [expenseType], Set.empty, Map.empty⟩
def schema : Schema :=
  ⟨Map.make [(userType, userEntry), (groupType, groupEntry),
      (expenseType, expenseEntry)],
    Map.make [(listTeam, actionEntry), (reject, actionEntry)]⟩

def request (principal action resource : EntityUID) : Request :=
  ⟨principal, action, resource, Map.empty⟩

def attr (subject : Cedar.Spec.Var) (name : String) : Expr :=
  .getAttr (.var subject) name
def unequal (left right : Expr) : Expr :=
  .unaryApp .not (.binaryApp .eq left right)
def condition (body : Expr) : Conditions := [{ kind := .when, body }]

/-- A diagnostic Cedar approximation of the source tool's unconstrained
    list/reject behavior. The source does not deploy this policy. -/
def exposed : Policy :=
  { id := "expense-exposure", effect := .permit,
    principalScope := .principalScope (.is userType),
    actionScope := .actionInAny [listTeam, reject],
    resourceScope := .resourceScope (.is expenseType), condition := [] }

def veto (id : String) (action : EntityUID) (body : Expr) : Policy :=
  { id, effect := .forbid,
    principalScope := .principalScope (.is userType),
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope (.is expenseType),
    condition := condition body }

structure DepartmentSetting where
  policyId : String
  action : EntityUID

def departmentVeto (setting : DepartmentSetting) : Policy :=
  veto setting.policyId setting.action
    (unequal (attr .principal "department") (attr .resource "department"))

def teamDepartmentProfile : CedarPooSpec.PolicyProfile.Object DepartmentSetting :=
  (CedarPooSpec.PolicyProfile.define "TeamDepartment"
    { policyId := "team-row-boundary", action := listTeam } departmentVeto)
    |>.toOption.get (by native_decide)

def rejectionDepartmentProfile : CedarPooSpec.PolicyProfile.Object DepartmentSetting :=
  (CedarPooSpec.PolicyProfile.revise teamDepartmentProfile
    "RejectionDepartment"
    { policyId := "reject-department-boundary", action := reject })
    |>.toOption.get (by native_decide)

def crossDepartment : Policy :=
  (CedarPooSpec.PolicyProfile.policy? teamDepartmentProfile).get
    (by native_decide)
def rejectScope : Policy :=
  (CedarPooSpec.PolicyProfile.policy? rejectionDepartmentProfile).get
    (by native_decide)
def nonApprover : Policy :=
  veto "reject-role-boundary" reject
    (.unaryApp .not
      (.binaryApp .mem (.var .principal) (.lit (.entityUID approvers))))
def selfRejection : Policy :=
  veto "reject-duty-boundary" reject
    (.binaryApp .eq (attr .principal "email")
      (attr .resource "submitterEmail"))
def nonSubmitted : Policy :=
  veto "reject-state-boundary" reject
    (unequal (attr .resource "status") (.lit (.string "submitted")))
def frozenExpense : Policy :=
  veto "expense-incident-freeze" reject
    (.binaryApp .eq (.var .resource) (.lit (.entityUID salesExpense)))

def modelResult : Except LeanPoo.C4.Error Model := do
  let source : Model :=
    { modules := [{ name := "SourceProjection", edits := [.extend exposed] }] }
  let team ← source.extend "Team" "SourceProjection" [.extend crossDepartment]
  let scopeOwner ← team.extend "ApprovalScope" "SourceProjection" [.extend rejectScope]
  let roles ← scopeOwner.extend "Role" "SourceProjection" [.extend nonApprover]
  let duties ← roles.extend "Duties" "SourceProjection" [.extend selfRejection]
  let states ← duties.extend "State" "SourceProjection" [.extend nonSubmitted]
  let governed ← states.mix "Governed"
    ["Team", "ApprovalScope", "Role", "Duties", "State"]
  let incident ← governed.extend "Incident" "Governed" [.extend frozenExpense]
  incident.extend "Recovered" "Incident" [.remove frozenExpense.id]

/-- The same validated LeanPOO model drives Lean decisions and Cedar export. -/
def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

/-- The composition is the LeanPOO C4 order, not a handwritten conjunction
    of the five Cedar conditions. Each policy below comes from its own owner. -/

theorem governedComposition :
    LeanPoo.C4.linearize model.graph "Governed" =
      .ok ["Governed", "Team", "ApprovalScope", "Role", "Duties", "State",
        "SourceProjection"] ∧
    (model.compilePlan "Governed").toOption.map (·.plan.precedence) =
      some ["Governed", "Team", "ApprovalScope", "Role", "Duties", "State",
        "SourceProjection"] ∧
    (model.compileWithProvenance "Governed").toOption.map
      (·.map (fun p => (p.policy.id, p.introducedBy))) =
      some [(exposed.id, "SourceProjection"),
        (nonSubmitted.id, "State"), (selfRejection.id, "Duties"),
        (nonApprover.id, "Role"), (rejectScope.id, "ApprovalScope"),
        (crossDepartment.id, "Team")] := by
  native_decide

def decideAt
     (root : String) (req : Request)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AWS.Expense.model CedarPooSpec.AWS.Expense.schema :=
      CedarPooSpec.AWS.Expense.program) : Option Decision := do
  let response ← (programContext.response root req entities).toOption
  if response.erroringPolicies.isEmpty then some response.decision else none

/-- Named operation checks are shared by the Lean proof and official Cedar
    replay. Each root is compiled separately, as a deployment revision. -/
def cases : List (String × String × Request × Decision) := [
  ("source-cross-team-read", "SourceProjection", request alice listTeam financeExpense, .allow),
  ("source-self-reject", "SourceProjection", request alice reject salesExpense, .allow),
  ("source-other-team-reject", "SourceProjection", request bob reject salesExpense, .allow),
  ("source-approved-reject", "SourceProjection", request carol reject approvedExpense, .allow),
  ("team-cross-read", "Team", request alice listTeam financeExpense, .deny),
  ("team-own-read", "Team", request alice listTeam salesExpense, .allow),
  ("team-leaves-reject-open", "Team", request alice reject salesExpense, .allow),
  ("approval-scope-cross-reject", "ApprovalScope", request bob reject salesExpense, .deny),
  ("approval-scope-leaves-self-open", "ApprovalScope", request bob reject financeExpense, .allow),
  ("role-nonmanager-reject", "Role", request alice reject salesExpense, .deny),
  ("role-leaves-approved-open", "Role", request carol reject approvedExpense, .allow),
  ("duties-self-reject", "Duties", request bob reject financeExpense, .deny),
  ("duties-leaves-approved-open", "Duties", request carol reject approvedExpense, .allow),
  ("state-approved-reject", "State", request carol reject approvedExpense, .deny),
  ("state-leaves-cross-read-open", "State", request alice listTeam financeExpense, .allow),
  ("governed-cross-read", "Governed", request alice listTeam financeExpense, .deny),
  ("governed-own-read", "Governed", request alice listTeam salesExpense, .allow),
  ("governed-manager-cross-read", "Governed", request carol listTeam financeExpense, .deny),
  ("governed-valid-reject", "Governed", request carol reject salesExpense, .allow),
  ("governed-cross-reject", "Governed", request bob reject salesExpense, .deny),
  ("governed-self-reject", "Governed", request bob reject financeExpense, .deny),
  ("governed-nonmanager-reject", "Governed", request alice reject salesExpense, .deny),
  ("governed-approved-reject", "Governed", request carol reject approvedExpense, .deny),
  ("incident-frozen-reject", "Incident", request carol reject salesExpense, .deny),
  ("incident-read-unaffected", "Incident", request carol listTeam salesExpense, .allow),
  ("recovered-valid-reject", "Recovered", request carol reject salesExpense, .allow),
  ("recovered-self-still-denied", "Recovered", request bob reject financeExpense, .deny)]

theorem casesExact :
    cases.all (fun (_, root, req, expected) =>
      decideAt root req == some expected) = true := by
  native_decide

theorem independentOwnersNeeded :
    decideAt "SourceProjection" (request alice listTeam financeExpense) = some .allow ∧
    decideAt "Team" (request alice listTeam financeExpense) = some .deny ∧
    decideAt "Role" (request alice listTeam financeExpense) = some .allow ∧
    decideAt "Duties" (request alice reject salesExpense) = some .deny ∧
    decideAt "Role" (request alice reject salesExpense) = some .deny ∧
    decideAt "State" (request alice reject salesExpense) = some .allow := by
  native_decide

theorem governedAndIncident :
    decideAt "Governed" (request alice listTeam salesExpense) = some .allow ∧
    decideAt "Governed" (request alice listTeam financeExpense) = some .deny ∧
    decideAt "Governed" (request carol reject salesExpense) = some .allow ∧
    decideAt "Governed" (request bob reject salesExpense) = some .deny ∧
    decideAt "Governed" (request bob reject financeExpense) = some .deny ∧
    decideAt "Governed" (request carol reject approvedExpense) = some .deny ∧
    decideAt "Incident" (request carol reject salesExpense) = some .deny ∧
    decideAt "Recovered" (request carol reject salesExpense) = some .allow := by
  native_decide

theorem incidentLocality :
    ((model.compileRevision "Governed" "Incident").toOption.get
      (by native_decide)).changedPolicyIds = [frozenExpense.id] ∧
    (model.compile "Recovered" == model.compile "Governed") = true := by
  native_decide

theorem everyRootValid :
    ["SourceProjection", "Team", "ApprovalScope", "Role", "Duties", "State", "Governed",
      "Incident", "Recovered"].all (fun root =>
        (CedarPooSpec.AWS.Expense.program.publish root).isOk) = true := by
  native_decide

end CedarPooSpec.AWS.Expense
