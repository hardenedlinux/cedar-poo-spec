import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.Authorization.Compound

/-!
Three-layer agent authorization inspired by the AWS Cedar delegation sample.
Identity, context integrity, and tool execution remain host responsibilities.
-/

namespace CedarPooSpec.AgentDelegationExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules

def agentType : EntityType := ⟨"Agent", []⟩
def userType : EntityType := ⟨"User", []⟩
def roleType : EntityType := ⟨"Role", []⟩
def toolType : EntityType := ⟨"Tool", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def orchestrator : EntityUID := ⟨agentType, "orchestrator"⟩
def dataBot : EntityUID := ⟨agentType, "data-bot"⟩
def weakBot : EntityUID := ⟨agentType, "weak-bot"⟩
def admin : EntityUID := ⟨userType, "admin"⟩
def support : EntityUID := ⟨userType, "support"⟩
def adminNoMfa : EntityUID := ⟨userType, "admin-no-mfa"⟩
def missingUser : EntityUID := ⟨userType, "missing"⟩
def adminRole : EntityUID := ⟨roleType, "Admin"⟩
def supportRole : EntityUID := ⟨roleType, "Support"⟩
def deleteRecords : EntityUID := ⟨toolType, "delete-records"⟩
def exportRecords : EntityUID := ⟨toolType, "export-records"⟩
def invoke : EntityUID := ⟨actionType, "invoke"⟩
def delegate : EntityUID := ⟨actionType, "delegate"⟩
def verifyOrigin : EntityUID := ⟨actionType, "verify-origin"⟩

def agentData (trust : Int64) (domain stage : String) (capabilities : List String) : EntityData :=
  { attrs := Map.make [
      ("trust", .prim (.int trust)),
      ("namespace", .prim (.string domain)),
      ("stage", .prim (.string stage)),
      ("capabilities", .set (Set.make (capabilities.map (fun item => .prim (.string item)))))],
    ancestors := Set.empty, tags := Map.empty }

def userData (role : EntityUID) (mfa : Bool) : EntityData :=
  { attrs := Map.make [("mfa", .prim (.bool mfa))],
    ancestors := Set.make [role], tags := Map.empty }

def emptyData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }

def entities : Entities := Map.make [
  (orchestrator, agentData 5 "orchestration" "production" ["delegate"]),
  (dataBot, agentData 4 "data" "production" ["delete_records"]),
  (weakBot, agentData 2 "data" "staging" ["delete_records"]),
  (admin, userData adminRole true),
  (support, userData supportRole false),
  (adminNoMfa, userData adminRole false),
  (adminRole, emptyData), (supportRole, emptyData),
  (deleteRecords, emptyData), (exportRecords, emptyData),
  (invoke, emptyData), (delegate, emptyData), (verifyOrigin, emptyData)]

def agentEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("trust", .required .int),
    ("namespace", .required .string),
    ("stage", .required .string),
    ("capabilities", .required (.set .string))], none⟩
def userEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [roleType], Map.make [("mfa", .required (.bool .anyBool))], none⟩
def emptyEntry : EntitySchemaEntry := .standard ⟨Set.empty, Map.empty, none⟩
def toolActionEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [toolType], Set.empty, Map.empty⟩
def delegateActionEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [agentType], Set.empty,
    Map.make [("depth", .required .int), ("requestedCaps", .required (.set .string))]⟩
def originActionEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [toolType], Set.empty,
    Map.make [("depth", .required .int), ("origin", .required (.entity userType))]⟩
def schema : Schema :=
  ⟨Map.make [(agentType, agentEntry), (userType, userEntry),
    (roleType, emptyEntry), (toolType, emptyEntry)],
    Map.make [(invoke, toolActionEntry), (delegate, delegateActionEntry),
      (verifyOrigin, originActionEntry)]⟩

def ctx (name : String) : Expr := .getAttr (.var .context) name
def principalFact (name : String) : Expr := .getAttr (.var .principal) name
def resourceFact (name : String) : Expr := .getAttr (.var .resource) name
def eq (left right : Expr) : Expr := .binaryApp .eq left right

def toolBody : Expr :=
  .and (.binaryApp .lessEq (.lit (.int 3)) (principalFact "trust"))
    (.and (eq (principalFact "namespace") (.lit (.string "data")))
      (eq (principalFact "stage") (.lit (.string "production"))))
def delegationBody : Expr :=
  .and (.binaryApp .lessEq (ctx "depth") (.lit (.int 3)))
    (.binaryApp .containsAll (resourceFact "capabilities") (ctx "requestedCaps"))
def originRole : Expr :=
  .binaryApp .mem (ctx "origin") (.lit (.entityUID adminRole))
def originMfa : Expr := .getAttr (ctx "origin") "mfa"
def originBody : Expr :=
  .and originRole
    (.and originMfa (.binaryApp .lessEq (ctx "depth") (.lit (.int 2))))

def policy (id : String) (action : EntityUID) (principal resource : Scope)
    (body : Expr) : Policy :=
  { id, effect := .permit,
    principalScope := .principalScope principal,
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope resource,
    condition := [{ kind := .when, body }] }

def toolBase : Policy :=
  policy "agent-tool" invoke (.eq dataBot) (.eq deleteRecords) (.lit (.bool true))
def toolHardened : Policy :=
  { toolBase with condition := [{ kind := .when, body := toolBody }] }
def delegationBase : Policy :=
  policy "agent-delegation" delegate (.eq orchestrator) (.eq dataBot) (.lit (.bool true))
def delegationBounded : Policy :=
  { delegationBase with condition := [{ kind := .when, body := delegationBody }] }
def originBase : Policy :=
  policy "origin-user" verifyOrigin (.eq dataBot) (.eq deleteRecords) (.lit (.bool true))
def originBounded : Policy :=
  { originBase with condition := [{ kind := .when, body := originBody }] }
def originRevoked : Policy :=
  { id := "revoke-admin-origin", effect := .forbid,
    principalScope := .principalScope (.eq dataBot),
    actionScope := .actionScope (.eq verifyOrigin),
    resourceScope := .resourceScope (.eq deleteRecords),
    condition := [{ kind := .when, body := eq (ctx "origin") (.lit (.entityUID admin)) }] }

def originGuardBody : Expr :=
  .unaryApp .not (.binaryApp .mem (ctx "origin") (.lit (.entityUID adminRole)))
def originGuard : Policy :=
  { id := "origin-admin-guard", effect := .forbid,
    principalScope := .principalScope (.eq dataBot),
    actionScope := .actionScope (.eq verifyOrigin),
    resourceScope := .resourceScope (.eq deleteRecords),
    condition := [{ kind := .when, body := originGuardBody }] }

def modelResult : Except LeanPoo.C4.Error Model := do
  let tool : Model := { modules := [{ name := "ToolBase", edits := [.extend toolBase] }] }
  let hardened ← tool.extend "ToolHardened" "ToolBase" [.overlay toolHardened]
  let delegation ← hardened.mix "DelegationBase" [] [.extend delegationBase]
  let bounded ← delegation.extend "DelegationBounded" "DelegationBase"
    [.overlay delegationBounded]
  let origin ← bounded.mix "OriginBase" [] [.extend originBase]
  let originBound ← origin.extend "OriginBounded" "OriginBase" [.overlay originBounded]
  let revoked ← originBound.extend "OriginRevoked" "OriginBounded"
    [.extend originRevoked]
  revoked.extend "OriginUnsafe" "OriginBase" [.extend originGuard]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

def requestTool (agent tool : EntityUID) : Request :=
  ⟨agent, invoke, tool, Map.empty⟩
def requestDelegate (agent : EntityUID) (depth : Int64) (capability : String) : Request :=
  ⟨orchestrator, delegate, agent, Map.make [
    ("depth", .prim (.int depth)),
    ("requestedCaps", .set (Set.make [.prim (.string capability)]))]⟩
def requestOrigin (agent tool origin : EntityUID) (depth : Int64) : Request :=
  ⟨agent, verifyOrigin, tool, Map.make [
    ("depth", .prim (.int depth)), ("origin", .prim (.entityUID origin))]⟩

structure Roots where
  tool : String
  delegation : String
  origin : String

def legacy : Roots := ⟨"ToolBase", "DelegationBase", "OriginBase"⟩
def governed : Roots := ⟨"ToolHardened", "DelegationBounded", "OriginBounded"⟩
def revoked : Roots := { governed with origin := "OriginRevoked" }
def unsafeRoots : Roots := { governed with origin := "OriginUnsafe" }

def checks (roots : Roots) (agent tool origin : EntityUID) (depth : Int64)
    (capability : String) : List (String × Request) := [
  (roots.tool, requestTool agent tool),
  (roots.delegation, requestDelegate agent depth capability),
  (roots.origin, requestOrigin agent tool origin depth)]

def authorizeFlow
     (roots : Roots) (agent tool origin : EntityUID) (depth : Int64)
    (capability : String)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDelegationExample.model CedarPooSpec.AgentDelegationExample.schema :=
      CedarPooSpec.AgentDelegationExample.program) : Bool :=
  match programContext.authorizeLayers
      (checks roots agent tool origin depth capability) entities with
  | .error _ => false
  | .ok receipts => CedarPooSpec.Authorization.Compound.layersAllowed receipts

def flowCases : List (String × Roots × EntityUID × EntityUID × EntityUID × Int64 × String × Bool) := [
  ("legacy-support-delete", legacy, dataBot, deleteRecords, support, 2, "delete_records", true),
  ("governed-admin", governed, dataBot, deleteRecords, admin, 2, "delete_records", true),
  ("governed-support", governed, dataBot, deleteRecords, support, 2, "delete_records", false),
  ("governed-admin-no-mfa", governed, dataBot, deleteRecords, adminNoMfa, 2, "delete_records", false),
  ("governed-depth-six", governed, dataBot, deleteRecords, admin, 6, "delete_records", false),
  ("governed-unregistered-capability", governed, dataBot, deleteRecords, admin, 2, "exfiltrate", false),
  ("governed-weak-agent", governed, weakBot, deleteRecords, admin, 2, "delete_records", false),
  ("governed-wrong-tool", governed, dataBot, exportRecords, admin, 2, "delete_records", false),
  ("governed-missing-user", governed, dataBot, deleteRecords, missingUser, 2, "delete_records", false),
  ("revoked-admin", revoked, dataBot, deleteRecords, admin, 2, "delete_records", false)]

def flowsExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDelegationExample.model CedarPooSpec.AgentDelegationExample.schema :=
      CedarPooSpec.AgentDelegationExample.program) : Bool := flowCases.all fun (_, roots, agent, tool, origin, depth, capability, expected) =>
  (authorizeFlow (programContext := programContext)) roots agent tool origin depth capability == expected

theorem flowsExactFully : flowsExact = true := by native_decide

def malformedOrigin : Request :=
  ⟨dataBot, verifyOrigin, deleteRecords, Map.make [
    ("depth", .prim (.int 2)), ("origin", .prim (.string "admin"))]⟩

def malformedChecks : List (String × Request) := [
  ("ToolHardened", requestTool dataBot deleteRecords),
  ("DelegationBounded", requestDelegate dataBot 2 "delete_records"),
  ("OriginUnsafe", malformedOrigin)]

def malformedRawResponse : Bool :=
  match model.compile "OriginUnsafe" with
  | .error _ => false
  | .ok policies =>
      let response := isAuthorized malformedOrigin entities policies
      response.decision == .allow && response.erroringPolicies.contains "origin-admin-guard"

theorem malformedRawAllowsWithError : malformedRawResponse = true := by native_decide

def malformedFlowRejected
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDelegationExample.model CedarPooSpec.AgentDelegationExample.schema :=
      CedarPooSpec.AgentDelegationExample.program) : Bool :=
  match programContext.authorizeLayers malformedChecks entities with
  | .error _ => false
  | .ok receipts => !CedarPooSpec.Authorization.Compound.layersAllowed receipts

theorem malformedFlowRejectedFully : malformedFlowRejected = true := by native_decide

def allRootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDelegationExample.model CedarPooSpec.AgentDelegationExample.schema :=
      CedarPooSpec.AgentDelegationExample.program) : Bool :=
  ["ToolBase", "ToolHardened", "DelegationBase", "DelegationBounded",
   "OriginBase", "OriginBounded", "OriginRevoked", "OriginUnsafe"].all fun root =>
    (programContext.publish root).isOk

theorem allRootsValidatedFully : allRootsValidated = true := by native_decide

end CedarPooSpec.AgentDelegationExample
