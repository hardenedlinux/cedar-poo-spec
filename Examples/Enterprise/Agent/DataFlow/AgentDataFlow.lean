import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Delegation.AgentDelegation
import LeanPoo.Object.Multimethod

/-!
An agent's right to read a document does not imply a right to publish its
contents to a repository. Both decisions use one caller-supplied entity store.
-/

namespace CedarPooSpec.AgentDataFlowExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.AgentDelegationExample

def documentType : EntityType := ⟨"Document", []⟩
def repositoryType : EntityType := ⟨"Repository", []⟩
def securityRole : EntityUID := ⟨roleType, "Security"⟩
def knowledgeBot : EntityUID := ⟨agentType, "knowledge-bot"⟩
def reviewer : EntityUID := ⟨userType, "reviewer"⟩
def internalDoc : EntityUID := ⟨documentType, "internal"⟩
def publicDoc : EntityUID := ⟨documentType, "public"⟩
def foreignDoc : EntityUID := ⟨documentType, "foreign"⟩
def internalRepo : EntityUID := ⟨repositoryType, "internal"⟩
def publicRepo : EntityUID := ⟨repositoryType, "public"⟩
def foreignRepo : EntityUID := ⟨repositoryType, "foreign"⟩
def readDocument : EntityUID := ⟨actionType, "read-document"⟩
def publishDocument : EntityUID := ⟨actionType, "publish-document"⟩

def classified (tenant classification : String) : EntityData :=
  { emptyData with attrs := Map.make [
      ("tenant", .prim (.string tenant)),
      ("classification", .prim (.string classification))] }
def destination (tenant visibility : String) : EntityData :=
  { emptyData with attrs := Map.make [
      ("tenant", .prim (.string tenant)),
      ("visibility", .prim (.string visibility))] }
def dataEntities : Entities := Map.make (entities.toList ++ [
  (knowledgeBot, agentData 4 "knowledge" "production" ["read", "publish"]),
  (securityRole, emptyData),
  (reviewer, { userData adminRole true with ancestors := Set.make [adminRole, securityRole] }),
  (internalDoc, classified "acme" "internal"),
  (publicDoc, classified "acme" "public"),
  (foreignDoc, classified "other" "internal"),
  (internalRepo, destination "acme" "internal"),
  (publicRepo, destination "acme" "public"),
  (foreignRepo, destination "other" "public"),
  (readDocument, emptyData), (publishDocument, emptyData)])

def documentEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("tenant", .required .string), ("classification", .required .string)], none⟩
def repositoryEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("tenant", .required .string), ("visibility", .required .string)], none⟩
def readEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [documentType], Set.empty,
    Map.make [("origin", .required (.entity userType))]⟩
def publishEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [repositoryType], Set.empty,
    Map.make [("source", .required (.entity documentType)),
      ("origin", .required (.entity userType)),
      ("reviewer", .required (.entity userType)),
      ("approved", .required (.bool .anyBool))]⟩
def dataSchema : Schema :=
  ⟨Map.make (schema.ets.toList ++ [
      (documentType, documentEntry), (repositoryType, repositoryEntry)]),
    Map.make (schema.acts.toList ++ [
      (readDocument, readEntry), (publishDocument, publishEntry)])⟩

def sourceFact (name : String) : Expr := .getAttr (ctx "source") name
def dataTenant : Expr :=
  .and (eq (resourceFact "tenant") (.lit (.string "acme")))
    (.binaryApp .mem (ctx "origin") (.lit (.entityUID adminRole)))
def destinationTenant : Expr :=
  eq (resourceFact "tenant") (sourceFact "tenant")
def internalDestination : Expr :=
  eq (resourceFact "visibility") (.lit (.string "internal"))
def publicSource : Expr :=
  eq (sourceFact "classification") (.lit (.string "public"))
def classificationBoundary : Expr :=
  .or internalDestination publicSource
def independentReview : Expr :=
  .and (ctx "approved")
    (.and (.binaryApp .mem (ctx "reviewer") (.lit (.entityUID securityRole)))
      (.and (.getAttr (ctx "reviewer") "mfa")
        (.unaryApp .not (eq (ctx "reviewer") (ctx "origin")))))
def readBase : Policy :=
  policy "agent-document-read" readDocument (.eq knowledgeBot) .any (.lit (.bool true))
def readTenant : Policy :=
  { readBase with condition := [{ kind := .when, body := dataTenant }] }
def publishBase : Policy :=
  policy "agent-document-publish" publishDocument (.eq knowledgeBot) .any (.lit (.bool true))
def publishScoped : Policy :=
  { publishBase with condition := [{ kind := .when, body := destinationTenant }] }
def publishVeto (id : String) (invalid : Expr) : Policy :=
  { id, effect := .forbid,
    principalScope := publishBase.principalScope,
    actionScope := publishBase.actionScope,
    resourceScope := publishBase.resourceScope,
    condition := [{ kind := .when, body := invalid }] }
def classificationVeto : Policy :=
  publishVeto "classification-boundary" (.unaryApp .not classificationBoundary)
def reviewVeto : Policy :=
  publishVeto "public-review"
    (.and (.unaryApp .not internalDestination)
      (.unaryApp .not independentReview))
def publicDocumentRevoked : Policy :=
  { id := "revoke-public-document-publication", effect := .forbid,
    principalScope := .principalScope (.eq knowledgeBot),
    actionScope := .actionScope (.eq publishDocument),
    resourceScope := .resourceScope .any,
    condition := [
      { kind := .when, body := eq (ctx "source") (.lit (.entityUID publicDoc)) }] }

/- Policy construction has two independent extension axes. The generic
   selects owner contributions; Cedar still evaluates the resulting policies
   against every request. A restricted source inherits both Internal and
   Regulated through C4, while a partner-public sink inherits Public. -/
def sourceClasses : LeanPoo.C4.Graph := { nodes := [
  { name := "Source" },
  { name := "Internal", parentOrders := [["Source"]] },
  { name := "Regulated", parentOrders := [["Source"]] },
  { name := "Restricted", parentOrders := [["Internal", "Regulated"]] },
  { name := "Public", parentOrders := [["Source"]] }] }

def destinationClasses : LeanPoo.C4.Graph := { nodes := [
  { name := "Destination" },
  { name := "Internal", parentOrders := [["Destination"]] },
  { name := "Public", parentOrders := [["Destination"]] },
  { name := "PartnerPublic", parentOrders := [["Public"]] }] }

private abbrev ControlShape := List String × List String

private def controlGeneric :
    LeanPoo.Object.Multimethod ControlShape Edit (List Edit) :=
  { arity := 2
    -- The published C4 root visits Review before Classified. Keep that
    -- policy order so proof reuse and JSON export see identical lists.
    precedence := fun shape => [shape.2, shape.1]
    combine := fun methods _ => methods.toList }

private def registeredControls : Except LeanPoo.Object.MultimethodError
    (LeanPoo.Object.Multimethod ControlShape Edit (List Edit)) := do
  let sourceOwner ← controlGeneric.register
    [.any, .prototype "Internal"] (.extend classificationVeto)
  sourceOwner.register [.prototype "Public", .any] (.extend reviewVeto)

/-- Keep profile-graph and method-arity errors visible to policy authors. -/
inductive ControlError where
  | sourceProfile (error : LeanPoo.C4.Error)
  | destinationProfile (error : LeanPoo.C4.Error)
  | method (error : LeanPoo.Object.MultimethodError)
  deriving Repr

/-- Build the Cedar policy edits for a pair of C4 profile classes. No request
    is authorized by this dispatch; it only constructs policy modules. -/
def controlEdits (source destination : String) : Except ControlError (List Edit) := do
  let sourceOrder ← (LeanPoo.C4.linearize sourceClasses source).mapError .sourceProfile
  let destinationOrder ←
    (LeanPoo.C4.linearize destinationClasses destination).mapError .destinationProfile
  let generic ← registeredControls.mapError .method
  let (edits, _) ← (generic.call (sourceOrder, destinationOrder)).mapError .method
  return edits

private theorem classifiedEditsExist :
    (controlEdits "Internal" "Destination").toOption.isSome = true := by native_decide
private theorem reviewEditsExist :
    (controlEdits "Source" "Public").toOption.isSome = true := by native_decide
private theorem combinedEditsExist :
    (controlEdits "Restricted" "PartnerPublic").toOption.isSome = true := by
  native_decide

def classifiedEdits : List Edit :=
  (controlEdits "Internal" "Destination").toOption.get classifiedEditsExist
def reviewEdits : List Edit :=
  (controlEdits "Source" "Public").toOption.get reviewEditsExist
def combinedEdits : List Edit :=
  (controlEdits "Restricted" "PartnerPublic").toOption.get combinedEditsExist

def dataModelResult : Except LeanPoo.C4.Error Model := do
  let read : Model := { modules := [{ name := "ReadBase", edits := [.extend readBase] }] }
  let tenant ← read.extend "ReadTenant" "ReadBase" [.overlay readTenant]
  let publish ← tenant.mix "PublishBase" [] [.extend publishBase]
  let scopedModel ← publish.extend "PublishScoped" "PublishBase" [.overlay publishScoped]
  let classified ← scopedModel.extend "PublishClassified" "PublishScoped" classifiedEdits
  let review ← classified.extend "PublishReview" "PublishScoped" reviewEdits
  let governed ← review.mix "PublishGoverned" ["PublishClassified", "PublishReview"]
  let dispatched ← governed.extend "PublishDispatched" "PublishScoped" combinedEdits
  let revoked ← dispatched.extend "PublishRevoked" "PublishGoverned"
    [.extend publicDocumentRevoked]
  revoked.extend "PublishRestored" "PublishRevoked"
    [.remove publicDocumentRevoked.id]

def dataModel : Model := dataModelResult.toOption.get (by native_decide)

/-- Prepared against this exact model/schema; requests and entities remain current. -/
def program : CedarPooSpec.Functional.Program dataModel dataSchema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard dataModel dataSchema
    (dataModel.modules.map (·.name)) (by native_decide)

def readRequest (source origin : EntityUID) : Request :=
  ⟨knowledgeBot, readDocument, source, Map.make [
    ("origin", .prim (.entityUID origin))]⟩
def publishRequest (source repo origin approver : EntityUID) (approved : Bool) : Request :=
  ⟨knowledgeBot, publishDocument, repo, Map.make [
    ("source", .prim (.entityUID source)),
    ("origin", .prim (.entityUID origin)),
    ("reviewer", .prim (.entityUID approver)),
    ("approved", .prim (.bool approved))]⟩
def checks (readRoot publishRoot : String) (source repo origin approver : EntityUID)
    (approved : Bool) : List (String × Request) := [
  (readRoot, readRequest source origin),
  (publishRoot, publishRequest source repo origin approver approved)]
def authorizeFlow
     (readRoot publishRoot : String) (source repo origin approver : EntityUID)
    (approved : Bool)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Bool :=
  match programContext.authorizeLayers
      (checks readRoot publishRoot source repo origin approver approved) dataEntities with
  | .error _ => false
  | .ok receipts => CedarPooSpec.Authorization.Compound.layersAllowed receipts

def cases : List (String × String × String × EntityUID × EntityUID × EntityUID × EntityUID × Bool × Bool) := [
  ("legacy-internal-to-public", "ReadBase", "PublishBase", internalDoc, publicRepo, admin, support, false, true),
  ("read-foreign-tenant", "ReadTenant", "PublishBase", foreignDoc, internalRepo, admin, reviewer, true, false),
  ("scoped-internal-to-public", "ReadTenant", "PublishScoped", internalDoc, publicRepo, admin, reviewer, true, true),
  ("classified-internal-to-public", "ReadTenant", "PublishClassified", internalDoc, publicRepo, admin, reviewer, true, false),
  ("classified-public-without-review", "ReadTenant", "PublishClassified", publicDoc, publicRepo, admin, support, false, true),
  ("review-only-internal-leak", "ReadTenant", "PublishReview", internalDoc, publicRepo, admin, reviewer, true, true),
  ("reviewed-public", "ReadTenant", "PublishGoverned", publicDoc, publicRepo, admin, reviewer, true, true),
  ("reviewed-unapproved", "ReadTenant", "PublishGoverned", publicDoc, publicRepo, admin, reviewer, false, false),
  ("reviewed-wrong-role", "ReadTenant", "PublishGoverned", publicDoc, publicRepo, admin, support, true, false),
  ("reviewed-self-approval", "ReadTenant", "PublishGoverned", publicDoc, publicRepo, reviewer, reviewer, true, false),
  ("internal-to-internal", "ReadTenant", "PublishGoverned", internalDoc, internalRepo, admin, support, false, true),
  ("cross-tenant-publish", "ReadTenant", "PublishGoverned", publicDoc, foreignRepo, admin, reviewer, true, false),
  ("unprivileged-origin", "ReadTenant", "PublishGoverned", publicDoc, publicRepo, support, reviewer, true, false),
  ("revoked-public-document", "ReadTenant", "PublishRevoked", publicDoc, publicRepo, admin, reviewer, true, false),
  ("restored-public-document", "ReadTenant", "PublishRestored", publicDoc, publicRepo, admin, reviewer, true, true)]

def casesExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Bool := cases.all fun (_, readRoot, publishRoot, source, repo,
    origin, approver, approved, expected) =>
  (authorizeFlow (programContext := programContext)) readRoot publishRoot source repo origin approver approved == expected
theorem casesExactFully : casesExact = true := by native_decide

def casesErrorFree
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Bool := cases.all fun (_, readRoot, publishRoot, source, repo,
    origin, approver, approved, _) =>
  match programContext.authorizeLayers
      (checks readRoot publishRoot source repo origin approver approved) dataEntities with
  | .error _ => false
  | .ok receipts => receipts.all fun layer => layer.response.erroringPolicies.isEmpty
theorem casesErrorFreeFully : casesErrorFree = true := by native_decide

def branchesNeedComposition
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Bool :=
  (authorizeFlow (programContext := programContext)) "ReadTenant" "PublishClassified" publicDoc publicRepo
      admin support false &&
  (authorizeFlow (programContext := programContext)) "ReadTenant" "PublishReview" internalDoc publicRepo
      admin reviewer true &&
  !(authorizeFlow (programContext := programContext)) "ReadTenant" "PublishGoverned" publicDoc publicRepo
      admin support false &&
  !(authorizeFlow (programContext := programContext)) "ReadTenant" "PublishGoverned" internalDoc publicRepo
      admin reviewer true
theorem branchesNeedCompositionFully : branchesNeedComposition = true := by
  native_decide

theorem classificationBranchLocal :
    ((dataModel.compileRevision "PublishScoped" "PublishClassified").toOption.get
      (by native_decide)).changedPolicyIds = ["classification-boundary"] := by
  native_decide
theorem reviewBranchLocal :
    ((dataModel.compileRevision "PublishScoped" "PublishReview").toOption.get
      (by native_decide)).changedPolicyIds = ["public-review"] := by native_decide
def governedPolicyIds : Bool :=
  match dataModel.compile "PublishGoverned" with
  | .error _ => false
  | .ok policies =>
      let ids := policies.map Policy.id
      ids.length == 3 &&
      ["agent-document-publish", "classification-boundary", "public-review"].all
        ids.contains
theorem governedPolicyIdsFully : governedPolicyIds = true := by native_decide

theorem revokeEditLocal :
    ((dataModel.compileRevision "PublishGoverned" "PublishRevoked").toOption.get
      (by native_decide)).changedPolicyIds = ["revoke-public-document-publication"] := by
  native_decide
theorem restoreEditLocal :
    ((dataModel.compileRevision "PublishRevoked" "PublishRestored").toOption.get
      (by native_decide)).changedPolicyIds = ["revoke-public-document-publication"] := by
  native_decide
theorem restoredPoliciesEqualGoverned :
    (dataModel.compile "PublishRestored" ==
      dataModel.compile "PublishGoverned") = true := by native_decide
theorem readRootUnchanged :
    (dataModel.compile "ReadTenant" ==
      ({ modules := dataModel.modules.take 2 } : Model).compile "ReadTenant") = true := by
  native_decide

def malformedReviewRequest : Request :=
  ⟨knowledgeBot, publishDocument, publicRepo, Map.make [
    ("source", .prim (.entityUID publicDoc)),
    ("origin", .prim (.entityUID admin)),
    ("reviewer", .prim (.string "reviewer")),
    ("approved", .prim (.bool true))]⟩
def malformedChecks : List (String × Request) := [
  ("ReadTenant", readRequest publicDoc admin),
  ("PublishGoverned", malformedReviewRequest)]
def malformedReviewRejected
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Bool :=
  match programContext.authorizeLayers
      malformedChecks dataEntities with
  | .ok [readLayer, publishLayer] =>
      publishLayer.response.decision == .allow &&
      !publishLayer.response.erroringPolicies.isEmpty &&
      !CedarPooSpec.Authorization.Compound.layersAllowed [readLayer, publishLayer]
  | _ => false
theorem malformedReviewRejectedFully : malformedReviewRejected = true := by
  native_decide

def classifiedLeakBoundary
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Bool :=
  match programContext.authorizeLayers
      (checks "ReadTenant" "PublishClassified" internalDoc publicRepo admin reviewer true)
      dataEntities with
  | .error _ => false
  | .ok [readLayer, publishLayer] =>
      readLayer.response.decision == .allow && publishLayer.response.decision == .deny
  | .ok _ => false
theorem classifiedLeakBoundaryFully : classifiedLeakBoundary = true := by native_decide

def allRootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgentDataFlowExample.dataModel CedarPooSpec.AgentDataFlowExample.dataSchema :=
      CedarPooSpec.AgentDataFlowExample.program) : Bool :=
  ["ReadBase", "ReadTenant", "PublishBase", "PublishScoped",
    "PublishClassified", "PublishReview", "PublishGoverned", "PublishDispatched",
    "PublishRevoked", "PublishRestored"].all fun root =>
      (programContext.publish root).isOk
theorem allRootsValidatedFully : allRootsValidated = true := by native_decide

end CedarPooSpec.AgentDataFlowExample
