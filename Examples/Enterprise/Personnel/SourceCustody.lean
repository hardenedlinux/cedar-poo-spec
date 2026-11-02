import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Governance.Personnel.AssetAccess
import CedarPooSpec.Governance.Personnel.Status
import CedarPooSpec.Governance.Personnel.Assignment
import CedarPooSpec.Governance.Personnel.KnowledgeScope
import CedarPooSpec.Governance.ScopedApproval
import CedarPooSpec.PolicyModules
import Cedar.Validation

/-!
One source-custody model serves a small startup and a larger organization.
The example uses synthetic identities and Host-attested snapshots. It proves
decisions about mediated operations, not control of an already cloned copy.
-/

namespace CedarPooSpec.SourceCustodyExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Governance
open CedarPooSpec.Governance.Personnel.AssetAccess

def userType : EntityType := ⟨"User", []⟩
def agentType : EntityType := ⟨"Agent", []⟩
def deviceType : EntityType := ⟨"Device", []⟩
def assetType : EntityType := ⟨"SourceAsset", []⟩
def sinkType : EntityType := ⟨"Destination", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def founder : EntityUID := ⟨userType, "founder"⟩
def researcher : EntityUID := ⟨userType, "researcher"⟩
def researcherB : EntityUID := ⟨userType, "researcher-b"⟩
def intern : EntityUID := ⟨userType, "intern"⟩
def partner : EntityUID := ⟨userType, "partner"⟩
def codingAgent : EntityUID := ⟨agentType, "coding-agent"⟩
def managedLaptop : EntityUID := ⟨deviceType, "managed-laptop"⟩
def stolenLaptop : EntityUID := ⟨deviceType, "stolen-laptop"⟩
def sharedSource : EntityUID := ⟨assetType, "shared-library"⟩
def researchASource : EntityUID := ⟨assetType, "research-a-code"⟩
def researchBSource : EntityUID := ⟨assetType, "research-b-code"⟩
def researchBInterface : EntityUID := ⟨assetType, "research-b-interface"⟩
def coreSource : EntityUID := ⟨assetType, "product-source"⟩
def sourceSlice : EntityUID := ⟨assetType, "pricing-component"⟩
def crownSource : EntityUID := ⟨assetType, "model-weights"⟩
def internalSink : EntityUID := ⟨sinkType, "organization"⟩
def localCheckout : EntityUID := ⟨sinkType, "managed-local-checkout"⟩
def externalSink : EntityUID := ⟨sinkType, "external-repository"⟩
def competitorSink : EntityUID := ⟨sinkType, "competitor"⟩
def read : EntityUID := ⟨actionType, "read"⟩
def download : EntityUID := ⟨actionType, "download"⟩
def transfer : EntityUID := ⟨actionType, "transfer"⟩

def emptyData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }
def member (engagement : Personnel.Engagement) (projects : List String)
    (stage : Personnel.Status.Stage := .active) : EntityData :=
  (⟨engagement, projects, stage⟩ : Personnel.Assignment).entityData
def asset (tier project : String) : EntityData :=
  { emptyData with attrs := Map.make [
      ("tier", .prim (.string tier)),
      ("project", .prim (.string project))] }
def sink (internal : Bool) : EntityData :=
  { emptyData with attrs := Map.make [("internal", .prim (.bool internal))] }

def contextType : RecordType := Map.make [
  ("origin", .required (.entity userType)),
  ("device", .required (.entity deviceType)),
  ("deviceTrusted", .required (.bool .anyBool)),
  ("delegationValid", .required (.bool .anyBool)),
  ("approvalValid", .required (.bool .anyBool)),
  ("incident", .required (.bool .anyBool)),
  ("destination", .required (.entity sinkType)),
  ("purpose", .required .string),
  ("epoch", .required .string)]
def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [userType, agentType], Set.make [assetType], Set.empty, contextType⟩
def emptyEntry : EntitySchemaEntry := .standard ⟨Set.empty, Map.empty, none⟩
def userEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("engagement", .required .string),
    ("projects", .required (.set .string)),
    ("employmentStage", .required .string)], none⟩
def assetEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("tier", .required .string),
    ("project", .required .string)], none⟩
def sinkEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [("internal", .required (.bool .anyBool))], none⟩
def schema : Schema :=
  ⟨Map.make [(userType, userEntry), (agentType, emptyEntry),
    (deviceType, emptyEntry),
    (assetType, assetEntry), (sinkType, sinkEntry)],
    Map.make [(read, actionEntry), (download, actionEntry),
      (transfer, actionEntry)]⟩
def entities : Entities := Map.make [
  (founder, member .core ["common", "product", "research-a", "research-b"]),
  (researcher, member .researcher ["common", "research-a"]),
  (researcherB, member .researcher ["common", "research-b"]),
  (intern, member .intern ["common", "research-a"]),
  (partner, member .researcher ["partner"]),
  (codingAgent, emptyData),
  (managedLaptop, emptyData), (stolenLaptop, emptyData),
  (sharedSource, asset "shared" "common"),
  (researchASource, asset "research" "research-a"),
  (researchBSource, asset "research" "research-b"),
  (researchBInterface, asset "interface" "research-b"),
  (coreSource, asset "product" "product"),
  (sourceSlice, asset "product" "product"),
  (crownSource, asset "restricted" "restricted"),
  (internalSink, sink true), (localCheckout, sink true),
  (externalSink, sink false),
  (competitorSink, sink false),
  (read, actionSchemaEntryToEntityData actionEntry),
  (download, actionSchemaEntryToEntityData actionEntry),
  (transfer, actionSchemaEntryToEntityData actionEntry)]
def withFounderStage (stage : Personnel.Status.Stage) : Entities :=
  Map.make ((entities.toList.filter (fun entry => entry.1 != founder)) ++
    [(founder, member .core ["common", "product", "research-a", "research-b"] stage)])
def departingEntities : Entities := withFounderStage .departureWindow
def separatedEntities : Entities := withFounderStage .separated

def ctx (name : String) : Expr := .getAttr (.var .context) name
def attr (value : Expr) (name : String) : Expr := .getAttr value name
def eq (left right : Expr) : Expr := .binaryApp .eq left right
def originAttr (name : String) : Expr := attr (ctx "origin") name
def engagementIs (name : String) : Expr :=
  eq (originAttr "engagement") (.lit (.string name))
def assignedProject : Expr :=
  .binaryApp .contains (originAttr "projects")
    (attr (.var .resource) "project")
def permitFor (id : String) (action : EntityUID) (body : Expr) : Policy :=
  { id, effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body }] }

def readGrant : Policy := permitFor "read-by-assignment" read
  (.or (eq (attr (.var .resource) "tier") (.lit (.string "shared")))
    (.and assignedProject
      (.and (.or (engagementIs "researcher") (engagementIs "core"))
        (.unaryApp .not
          (eq (attr (.var .resource) "tier") (.lit (.string "restricted")))))))
def downloadGrant : Policy := permitFor "download-by-assignment" download
  (.and (attr (ctx "destination") "internal")
    (.and assignedProject
      (.or (engagementIs "core")
        (.and (engagementIs "researcher")
          (eq (attr (.var .resource) "tier") (.lit (.string "research")))))))
def interfaceGrant : Policy := permitFor "scoped-interface-collaboration" read
  (.and (engagementIs "researcher")
    (.and (ctx "approvalValid")
      (eq (attr (.var .resource) "tier") (.lit (.string "interface")))))
def transferGrant : Policy := permitFor "transfer-by-core" transfer
  (.and (engagementIs "core")
    (.or (attr (ctx "destination") "internal") (ctx "approvalValid")))
def partnerReadGrant : Policy := permitFor "approved-partner-read" read
  (.and (engagementIs "researcher") (ctx "approvalValid"))
def crownExternalVeto : Veto :=
  { policyId := "crown-external", actionScope := .actionScope (.eq transfer),
    denyWhen := .and
      (eq (attr (.var .resource) "tier") (.lit (.string "restricted")))
      (.unaryApp .not (attr (ctx "destination") "internal")) }
def incidentFreeze : Veto :=
  { policyId := "incident-freeze", actionScope := .actionScope (.eq transfer),
    denyWhen := .lit (.bool true) }

/- Independent owners compose once. A larger company adds a scoped
   cross-team grant; an incident adds a transfer-only veto. -/
def modelResult : Except LeanPoo.C4.Error Model := do
  let roots : Model := { modules := [
    { name := "Read", edits := [.extend readGrant] },
    { name := "Download", edits := [.extend downloadGrant] },
    { name := "Transfer", edits := [.extend transferGrant] }] }
  let base ← roots.mix "Base" ["Read", "Download", "Transfer"]
  let devices ← base.extend "Devices" "Base"
    [(deviceVeto "managed-device" (.actionScope .any)).edit .introduce]
  let agents ← devices.extend "Agents" "Base"
    [(delegationVeto "agent-delegation" (.actionScope .any)).edit .introduce]
  let assets ← agents.extend "Assets" "Base"
    [crownExternalVeto.edit .introduce,
      (incidentVeto "reported-incident" (.actionScope (.eq transfer))).edit .introduce]
  let people ← assets.extend "People" "Base"
    [(Personnel.Status.veto "departure-transfer" (.actionInAny [download, transfer])
        .departureWindow).edit .introduce,
      (Personnel.Status.veto "separated-access" (.actionScope .any)
        .separated).edit .introduce]
  let isolated ← people.mix "Isolated" ["Devices", "Agents", "Assets", "People"]
  let small ← isolated.extend "SmallTeam" "Isolated" [.extend interfaceGrant]
  let large ← small.extend "LargeTeam" "SmallTeam"
    [.extend partnerReadGrant]
  let incident ← large.extend "Incident" "LargeTeam"
    [incidentFreeze.edit .introduce]
  incident.extend "Recovered" "Incident" [.remove incidentFreeze.policyId]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Retain checked policies for this exact model/schema, never request decisions. -/
def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard model schema
    (model.modules.map (·.name)) (by native_decide)

def state (origin : EntityUID) : Snapshot :=
  { origin, device := managedLaptop, deviceTrusted := true,
    delegationValid := false, approvalValid := false,
    incident := false, epoch := 1 }
def effect (executor action asset destination : EntityUID)
    (purpose : String := "development") : Personnel.AssetAccess.Effect :=
  ⟨executor, action, asset, destination, purpose⟩
def releaseApproval : ScopedApproval :=
  { id := "release-1", approver := researcher, actor := founder,
    operation := transfer, purpose := "release",
    source := coreSource, target := externalSink,
    revision := 1, expiresAt := 20 }
def partnerApproval : ScopedApproval :=
  { id := "review-1", approver := founder, actor := partner,
    operation := read, purpose := "review",
    source := coreSource, target := internalSink,
    revision := 1, expiresAt := 20 }
def interfaceApproval : ScopedApproval :=
  { id := "research-interface", approver := researcherB, actor := researcher,
    operation := read, purpose := "integration",
    source := researchBInterface, target := internalSink,
    revision := 1, expiresAt := 20 }
def readDelegation : Personnel.Delegation :=
  { id := "founder-agent-read", origin := founder, agent := codingAgent,
    action := read, asset := coreSource, destination := internalSink,
    purpose := "development", revision := 1, expiresAt := 20 }
def releaseDelegation : Personnel.Delegation :=
  { id := "founder-agent-release", origin := founder, agent := codingAgent,
    action := transfer, asset := coreSource, destination := externalSink,
    purpose := "release", revision := 1, expiresAt := 20 }

def decisionIn
     (root : String) (store : Entities) (operation : Operation)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SourceCustodyExample.model CedarPooSpec.SourceCustodyExample.schema :=
      CedarPooSpec.SourceCustodyExample.program) : Bool :=
  match programContext.authorize root [operation.request] store with
  | .error _ => false
  | .ok receipt => receipt.allowed

def decision
     (root : String) (operation : Operation)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SourceCustodyExample.model CedarPooSpec.SourceCustodyExample.schema :=
      CedarPooSpec.SourceCustodyExample.program) : Bool :=
  (decisionIn (programContext := programContext)) root entities operation

def normalRead : Operation :=
  ⟨effect founder read coreSource internalSink, state founder⟩
def stolenRead : Operation :=
  ⟨normalRead.effect,
    { state founder with device := stolenLaptop, deviceTrusted := false }⟩
def researcherRead : Operation :=
  ⟨effect researcher read sharedSource internalSink, state researcher⟩
def researcherCrown : Operation :=
  ⟨effect researcher read crownSource internalSink, state researcher⟩
def internSharedRead : Operation :=
  ⟨effect intern read sharedSource internalSink, state intern⟩
def internResearchRead : Operation :=
  ⟨effect intern read researchASource internalSink, state intern⟩
def internResearchDownload : Operation :=
  ⟨effect intern download researchASource localCheckout, state intern⟩
def researcherARead : Operation :=
  ⟨effect researcher read researchASource internalSink, state researcher⟩
def researcherAWrongProjectRead : Operation :=
  ⟨effect researcher read researchBSource internalSink, state researcher⟩
def researcherBRead : Operation :=
  ⟨effect researcherB read researchBSource internalSink, state researcherB⟩
def founderReadB : Operation :=
  ⟨effect founder read researchBSource internalSink, state founder⟩
def researcherAInterfaceRead : Operation :=
  let proposal := effect researcher read researchBInterface internalSink "integration"
  ⟨proposal, (state researcher).withApproval interfaceApproval proposal 10⟩
def researcherAFullBRead : Operation :=
  let proposal := effect researcher read researchBSource internalSink "integration"
  ⟨proposal, (state researcher).withApproval interfaceApproval proposal 10⟩
def researcherADownload : Operation :=
  ⟨effect researcher download researchASource localCheckout, state researcher⟩
def researcherBWrongDownload : Operation :=
  ⟨effect researcherB download researchASource localCheckout, state researcherB⟩
def founderDownload : Operation :=
  ⟨effect founder download coreSource localCheckout, state founder⟩
def founderCrownDownload : Operation :=
  ⟨effect founder download crownSource localCheckout, state founder⟩
def agentReadEffect : Personnel.AssetAccess.Effect :=
  effect codingAgent read coreSource internalSink
def agentReadWithoutDelegation : Operation :=
  ⟨agentReadEffect, state founder⟩
def agentReadWithDelegation : Operation :=
  ⟨agentReadEffect,
    (state founder).withDelegation readDelegation agentReadEffect 10⟩
def agentReadAfterExpiry : Operation :=
  ⟨agentReadEffect,
    (state founder).withDelegation readDelegation agentReadEffect 20⟩
def approvedRelease (epoch : Nat := 1) : Operation :=
  let transferEffect := effect founder transfer coreSource externalSink "release"
  let current := { state founder with epoch }
  ⟨transferEffect, current.withApproval releaseApproval transferEffect 10⟩
def attemptedExternalTransfer : Operation :=
  ⟨effect founder transfer coreSource externalSink "personal-copy", state founder⟩
def attemptedAgentTransfer : Operation :=
  let proposal := effect codingAgent transfer coreSource externalSink "personal-copy"
  ⟨proposal, (state founder).withDelegation readDelegation proposal 10⟩
def agentRelease (grant : Personnel.Delegation) : Operation :=
  let proposal := effect codingAgent transfer coreSource externalSink "release"
  let authorized := (state founder).withApproval releaseApproval proposal 10
  ⟨proposal, authorized.withDelegation grant proposal 10⟩
def attemptedPartialSale : Operation :=
  let sale := effect founder transfer sourceSlice competitorSink "sale"
  ⟨sale, (state founder).withApproval releaseApproval sale 10⟩
def normalSliceRead : Operation :=
  ⟨effect founder read sourceSlice internalSink, state founder⟩
def crownRelease : Operation :=
  let transferEffect := effect founder transfer crownSource externalSink "release"
  ⟨transferEffect, (state founder).withApproval releaseApproval transferEffect 10⟩
def partnerReadOperation : Operation :=
  let readEffect := effect partner read coreSource internalSink "review"
  ⟨readEffect, (state partner).withApproval partnerApproval readEffect 10⟩
def partnerRead
     (root : String)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.SourceCustodyExample.model CedarPooSpec.SourceCustodyExample.schema :=
      CedarPooSpec.SourceCustodyExample.program) : Bool :=
  (decision (programContext := programContext)) root partnerReadOperation
def incidentRelease : Operation :=
  let current := approvedRelease 1
  ⟨current.effect, { current.state with incident := true }⟩

/- Asset owners curate these hypothetical knowledge claims. The access model
   is checked by Cedar; this assessment compares what a completed task could
   reveal from the person's cumulative, observed assets. -/
def knowledgeCatalog : List
    (Personnel.KnowledgeScope.Fragment EntityUID String) := [
  ⟨researchASource, ["a-implementation"]⟩,
  ⟨researchBInterface, ["b-contract"]⟩,
  ⟨researchBSource, ["b-contract", "b-implementation"]⟩]
def integrationTask : Personnel.KnowledgeScope.Task String :=
  ⟨["a-implementation", "b-contract"]⟩
def architectureBoundary : Personnel.KnowledgeScope.Boundary String :=
  ⟨[["a-implementation", "b-implementation"]]⟩
def isolatedExposure : Personnel.KnowledgeScope.Ledger EntityUID :=
  ⟨[researchASource]⟩
def interfaceExposure : Personnel.KnowledgeScope.Ledger EntityUID :=
  isolatedExposure.observe researchBInterface
def fullSourceExposure : Personnel.KnowledgeScope.Ledger EntityUID :=
  isolatedExposure.observe researchBSource
def isolatedAssessment : Personnel.KnowledgeScope.Assessment :=
  Personnel.KnowledgeScope.assess knowledgeCatalog isolatedExposure
    integrationTask architectureBoundary
def interfaceAssessment : Personnel.KnowledgeScope.Assessment :=
  Personnel.KnowledgeScope.assess knowledgeCatalog interfaceExposure
    integrationTask architectureBoundary
def fullSourceAssessment : Personnel.KnowledgeScope.Assessment :=
  Personnel.KnowledgeScope.assess knowledgeCatalog fullSourceExposure
    integrationTask architectureBoundary

end CedarPooSpec.SourceCustodyExample
