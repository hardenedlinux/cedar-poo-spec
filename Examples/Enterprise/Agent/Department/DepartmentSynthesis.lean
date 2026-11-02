import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Fanout.CrossAgentEgress
import CedarPooSpec.SchemaJson

/-!
One delegated agent reads Sales and Finance records through separate owners.
Neither read is individually marked sensitive, but their joint result may not
be sent externally. This proposed workflow extends the existing cross-agent
history and budget model rather than copying its policies.
-/

namespace CedarPooSpec.DepartmentSynthesisExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules

def workerA : EntityUID := CedarPooSpec.CrossAgentEgressExample.workerA
def workerB : EntityUID := CedarPooSpec.CrossAgentEgressExample.workerB
def readAction : EntityUID := CedarPooSpec.CrossAgentEgressExample.readAction
def sendAction : EntityUID := CedarPooSpec.CrossAgentEgressExample.sendAction
def endpoint : EntityUID := CedarPooSpec.CrossAgentEgressExample.externalEndpoint
def documentType : EntityType := CedarPooSpec.BoundedSessionExample.documentType
def salesRecord : EntityUID := ⟨documentType, "sales-contract"⟩
def financeRecord : EntityUID := ⟨documentType, "finance-invoice"⟩

/-- Each department owns one record, one source-boundary policy, and one
    history fact. The governance graph and request projection use this list. -/
structure DepartmentObject where
  name : String
  record : EntityUID
  policyId : String
  seenFact : String

def sales : DepartmentObject :=
  ⟨"Sales", salesRecord, "sales-owner-boundary", "salesSeen"⟩
def finance : DepartmentObject :=
  ⟨"Finance", financeRecord, "finance-owner-boundary", "financeSeen"⟩
def departments : List DepartmentObject := [sales, finance]

def contextType : RecordType := Map.make
  (CedarPooSpec.CrossAgentEgressExample.contextType.toList ++
    departments.map (fun department =>
      (department.seenFact, .required (.bool .anyBool))) ++ [
    ("originDept", .required .string),
    ("delegationActive", .required (.bool .anyBool))])
def readEntry : ActionSchemaEntry :=
  ⟨Set.make [CedarPooSpec.BoundedSessionExample.agentType],
    Set.make [documentType], Set.empty, contextType⟩
def sendEntry : ActionSchemaEntry :=
  ⟨Set.make [CedarPooSpec.BoundedSessionExample.agentType],
    Set.make [CedarPooSpec.BoundedSessionExample.endpointType],
    Set.empty, contextType⟩
def documentEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("sensitive", .required (.bool .anyBool)),
    ("department", .required .string)], none⟩
def schema : Schema :=
  ⟨Map.make [
      (CedarPooSpec.BoundedSessionExample.agentType,
        CedarPooSpec.BoundedSessionExample.emptyEntry),
      (documentType, documentEntry),
      (CedarPooSpec.BoundedSessionExample.endpointType,
        CedarPooSpec.BoundedSessionExample.endpointEntry)],
    Map.make [(readAction, readEntry), (sendAction, sendEntry)]⟩

def documentData (department : String) : EntityData :=
  { CedarPooSpec.BoundedSessionExample.emptyData with attrs := Map.make [
      ("sensitive", .prim (.bool false)),
      ("department", .prim (.string department))] }
def entities : Entities := Map.make ([
  (workerA, CedarPooSpec.BoundedSessionExample.emptyData),
  (workerB, CedarPooSpec.BoundedSessionExample.emptyData)] ++
  departments.map (fun department =>
    (department.record, documentData department.name)) ++ [
  (endpoint, CedarPooSpec.BoundedSessionExample.endpointData true),
  (readAction, actionSchemaEntryToEntityData readEntry),
  (sendAction, actionSchemaEntryToEntityData sendEntry)])

def fact (name : String) : Expr := .getAttr (.var .context) name
def neq (left right : Expr) : Expr :=
  .unaryApp .not (.binaryApp .eq left right)
def DepartmentObject.veto (object : DepartmentObject) : Policy :=
  let body : Expr := .and
    (neq (fact "originDept") (.lit (.string object.name)))
    (neq (fact "originDept") (.lit (.string "Joint")))
  { id := object.policyId, effect := .forbid,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq readAction),
    resourceScope := .resourceScope (.eq object.record),
    condition := [{ kind := .when, body }] }
def seenExpression : List DepartmentObject → Expr
  | [] => .lit (.bool true)
  | [department] => fact department.seenFact
  | department :: rest => .and (fact department.seenFact) (seenExpression rest)
def aggregationVeto : Policy :=
  let body : Expr := seenExpression departments
  { id := "cross-department-aggregate-egress", effect := .forbid,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq sendAction),
    resourceScope := .resourceScope (.eq endpoint),
    condition := [{ kind := .when, body }] }
def expiredDelegationVeto : Policy :=
  let body : Expr := .unaryApp .not (fact "delegationActive")
  { id := "expired-delegation", effect := .forbid,
    principalScope := .principalScope .any,
    actionScope := .actionInAny [readAction, sendAction],
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body }] }

/-- Four independent owners extend the inherited cross-agent controls. -/
def modelResult : Except LeanPoo.C4.Error Model := do
  let base := CedarPooSpec.CrossAgentEgressExample.model
  let owned ← departments.foldlM (fun current department =>
    current.extend department.name "CrossAgentGoverned"
      [.extend department.veto]) base
  let aggregate ← owned.extend "Aggregate" "CrossAgentGoverned"
    [.extend aggregationVeto]
  let temporal ← aggregate.extend "Temporal" "CrossAgentGoverned"
    [.extend expiredDelegationVeto]
  let governed ← temporal.mix "DepartmentGoverned"
    (departments.map DepartmentObject.name ++ ["Aggregate", "Temporal"])
  let incident ← governed.mix "DepartmentIncident"
    ["DepartmentGoverned", "CrossAgentIncident"]
  incident.extend "DepartmentRecovered" "DepartmentIncident"
    [.remove CedarPooSpec.SharedBudgetExample.incidentVeto.id]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

/-- The composed root retains each new owner and the inherited history owner. -/

theorem composedOwnersPresent :
    (departments.map DepartmentObject.name ++
      ["Aggregate", "Temporal", "History"]).all (fun owner =>
      ((model.compileWithProvenance "DepartmentGoverned").toOption.get
        (by native_decide)).any (fun policy => policy.introducedBy == owner)) = true := by
  native_decide

/-- Each department contributes one policy; the aggregate and temporal
    owners add two more independently of the department count. -/
theorem revisionAddsFourPolicies :
    ((model.compileRevision "CrossAgentGoverned" "DepartmentGoverned").toOption.get
      (by native_decide)).changedPolicyIds.length = departments.length + 2 := by
  native_decide

theorem departmentObjectsBoundToSchemaAndEntities :
    departments.all (fun department =>
      contextType.contains department.seenFact &&
      entities.contains department.record) = true := by native_decide

structure State where
  lineage : CedarPooSpec.CrossAgentEgressExample.State := {}
  seen : List EntityUID := []
  originDept : String := "Joint"
  delegationActive : Bool := true

abbrev Attempt := CedarPooSpec.CrossAgentEgressExample.Attempt
def readSales : Attempt := ⟨workerA, readAction, salesRecord, "report"⟩
def readFinance : Attempt := ⟨workerA, readAction, financeRecord, "report"⟩
def sendReport : Attempt := ⟨workerB, sendAction, endpoint, "report"⟩

def request (state : State) (attempt : Attempt) : Request :=
  let base := CedarPooSpec.CrossAgentEgressExample.request
    .delegationShared state.lineage attempt
  { base with context := Map.make (base.context.toList ++
    departments.map (fun department =>
      (department.seenFact,
        .prim (.bool (state.seen.contains department.record)))) ++ [
      ("originDept", .prim (.string state.originDept)),
      ("delegationActive", .prim (.bool state.delegationActive))]) }

def authorized
     (root : String) (state : State) (attempt : Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.DepartmentSynthesisExample.model CedarPooSpec.DepartmentSynthesisExample.schema :=
      CedarPooSpec.DepartmentSynthesisExample.program) : Bool :=
  if attempt.worker != workerA && attempt.worker != workerB then false else
    match programContext.response root (request state attempt) entities with
    | .error _ => false
    | .ok response =>
        response.decision == .allow && response.erroringPolicies.isEmpty

def advance (state : State) (attempt : Attempt) : State :=
  let next := CedarPooSpec.CrossAgentEgressExample.advance state.lineage attempt
  { state with
    lineage := { next with epoch := state.lineage.epoch + 1 },
    seen := if attempt.action == readAction &&
        departments.any (fun department => department.record == attempt.resource) &&
        !state.seen.contains attempt.resource
      then attempt.resource :: state.seen else state.seen }

def replay
     (root : String) (initial : State) (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.DepartmentSynthesisExample.model CedarPooSpec.DepartmentSynthesisExample.schema :=
      CedarPooSpec.DepartmentSynthesisExample.program) :
    List (Request × Bool) × State :=
  let (state, rows) := attempts.foldl (fun (state, rows) attempt =>
    let req := request state attempt
    let allowed := (authorized (programContext := programContext)) root state attempt
    let next := if allowed then advance state attempt else state
    (next, rows ++ [(req, allowed)])) (initial, [])
  (rows, state)

def decisions
     (root : String) (state : State) (attempts : List Attempt)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.DepartmentSynthesisExample.model CedarPooSpec.DepartmentSynthesisExample.schema :=
      CedarPooSpec.DepartmentSynthesisExample.program) :
    List Bool := ((replay (programContext := programContext)) root state attempts).1.map Prod.snd

/-- Authority can change after an admitted read and before a proposed send. -/
def afterSalesThenRevoked
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.DepartmentSynthesisExample.model CedarPooSpec.DepartmentSynthesisExample.schema :=
      CedarPooSpec.DepartmentSynthesisExample.program) : State :=
  { ((replay (programContext := programContext)) "DepartmentGoverned" {} [readSales]).2 with
    delegationActive := false }

def cases
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.DepartmentSynthesisExample.model CedarPooSpec.DepartmentSynthesisExample.schema :=
      CedarPooSpec.DepartmentSynthesisExample.program) : List (String × String × State × List Attempt × List Bool) := [
  ("baseline-sales-reads-finance", "CrossAgentGoverned",
    { originDept := "Sales" }, [readFinance], [true]),
  ("sales-owner-alone-misses-finance", "Sales",
    { originDept := "Sales" }, [readFinance], [true]),
  ("finance-owner-closes-sales-leak", "DepartmentGoverned",
    { originDept := "Sales" }, [readFinance], [false]),
  ("sales-owner-closes-finance-leak", "DepartmentGoverned",
    { originDept := "Finance" }, [readSales], [false]),
  ("single-department-report", "DepartmentGoverned",
    {}, [readSales, sendReport], [true, true]),
  ("baseline-joint-result-egress", "CrossAgentGoverned",
    {}, [readSales, readFinance, sendReport], [true, true, true]),
  ("governed-joint-result-denied", "DepartmentGoverned",
    {}, [readSales, readFinance, sendReport], [true, true, false]),
  ("revoked-read-denied", "DepartmentGoverned",
    { delegationActive := false }, [readSales], [false]),
  ("revoked-send-denied", "DepartmentGoverned",
    { delegationActive := false }, [sendReport], [false]),
  ("revoked-after-read-denied", "DepartmentGoverned",
    (afterSalesThenRevoked (programContext := programContext)), [sendReport], [false]),
  ("incident-denies-unaffected-sales", "DepartmentIncident",
    {}, [readSales, sendReport], [true, false]),
  ("recovered-retains-aggregation", "DepartmentRecovered",
    {}, [readSales, readFinance, sendReport], [true, true, false]),
  ("recovered-allows-single-department", "DepartmentRecovered",
    {}, [readSales, sendReport], [true, true])]

theorem casesExact :
    cases.all (fun (_, root, state, attempts, expected) =>
      decisions root state attempts == expected) = true := by native_decide

theorem aggregationNeedsBothDepartments :
    decisions "DepartmentGoverned" {} [readSales, sendReport] = [true, true] ∧
    decisions "DepartmentGoverned" {} [readSales, readFinance, sendReport] =
      [true, true, false] := by native_decide

theorem revocationAfterRead :
    decisions "DepartmentGoverned" {} [readSales] = [true] ∧
    decisions "DepartmentGoverned" afterSalesThenRevoked [sendReport] = [false] := by
  native_decide

theorem allRootsValidate :
    (departments.map DepartmentObject.name ++
      ["Aggregate", "Temporal", "DepartmentGoverned",
        "DepartmentIncident", "DepartmentRecovered"]).all (fun root =>
        (CedarPooSpec.DepartmentSynthesisExample.program.publish root).isOk) = true := by
  native_decide

end CedarPooSpec.DepartmentSynthesisExample
