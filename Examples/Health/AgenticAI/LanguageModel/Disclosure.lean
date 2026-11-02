import CedarPooSpec.Data.LineageProfile
import CedarPooSpec.Functional.Capabilities
import Examples.Health.Pseudonymization
import CedarPooSpec.Data.DerivedArtifact
import CedarPooSpec.Data.CumulativeDisclosure
import CedarPooSpec.AgenticAI.Boundary
import CedarPooSpec.Governance.ScopedApproval
import CedarPooSpec.Governance.Personnel.Delegation
import LeanPoo.Object.Definition

/-!
A tool-using language-model system proposes publication of a result derived
from two hospital datasets through independent workspace and message channels.
The Cedar `agent` principal is its delegated execution identity; source labels,
approvals, and the shared release counter are Host-owned state.
-/

namespace CedarPooSpec.AgenticAI.LanguageModel.Disclosure

open Cedar.Spec Cedar.Data Cedar.Validation
open CedarPooSpec.PolicyModules CedarPooSpec.Governance CedarPooSpec.Data
open CedarPooSpec.AgenticAI
open CedarPooSpec.PseudonymizationExample

def sinkType : EntityType := ⟨"DisclosureSink", []⟩
def publish : EntityUID := ⟨actionType, "publish-derived-result"⟩
def studyWorkspace : EntityUID := ⟨sinkType, "study-workspace"⟩
def externalWorkspace : EntityUID := ⟨sinkType, "external-workspace"⟩

def sinkEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("tenant", .required .string),
    ("kind", .required .string)], none⟩
def publicationContext : RecordType := Map.make [
  ("lineageAllowed", .required (.bool .anyBool)),
  ("approvalActive", .required (.bool .anyBool)),
  ("delegationActive", .required (.bool .anyBool)),
  ("cohortSafe", .required (.bool .anyBool)),
  ("budgetAvailable", .required (.bool .anyBool)),
  ("audienceAllowed", .required (.bool .anyBool)),
  ("payloadBound", .required (.bool .anyBool)),
  ("auditReady", .required (.bool .anyBool))]
def publishEntry : ActionSchemaEntry :=
  ⟨Set.make [actorType], Set.make [sinkType], Set.empty, publicationContext⟩
def publicationSchema : Schema :=
  ⟨Map.make (schema.ets.toList ++ [(sinkType, sinkEntry)]),
    Map.make (schema.acts.toList ++ [(publish, publishEntry)])⟩
def sinkData (tenant kind : String) : EntityData :=
  { attrs := Map.make [("tenant", .prim (.string tenant)),
      ("kind", .prim (.string kind))],
    ancestors := Set.empty, tags := Map.empty }
def publicationEntities : Entities := Map.make (entities.toList ++ [
  (studyWorkspace, sinkData "hospital-a" "study"),
  (externalWorkspace, sinkData "outside" "external"),
  (publish, actionSchemaEntryToEntityData publishEntry)])

def source (resource : EntityUID) : SourceLabel :=
  { resource, owner := steward, tenant := "hospital-a", restricted := true }
abbrev LineageKey := CedarPooSpec.Data.LineageProfile.Key
abbrev LineageValue := CedarPooSpec.Data.LineageProfile.Value

/-- The inherited computation observes the final source list and digest. -/
def hospitalPrototype : Except (LeanPoo.Object.Dataflow.Error LineageKey)
    (LeanPoo.Object.Dataflow.Instance LineageKey LineageValue) :=
  LeanPoo.Object.Dataflow.defineStrict "HospitalLineage" do
    LeanPoo.Object.Dataflow.StrictBuilder.default .sources [source hospital]
    LeanPoo.Object.Dataflow.StrictBuilder.value .digest "hospital-result"
    LeanPoo.Object.Dataflow.StrictBuilder.derived .artifact
      ((fun sources digest => { digest, sources }) <$> LeanPoo.Object.Dataflow.Expr.need (Value := LineageValue) .sources
        <*> LeanPoo.Object.Dataflow.Expr.need (Value := LineageValue) .digest)

/-- A reusable research-source amendment composes with any compatible
    source prototype; it does not replace inherited provenance. -/
def researchAmendment : Except (LeanPoo.Object.Dataflow.Error LineageKey)
    (LeanPoo.Object.Dataflow.Instance LineageKey LineageValue) :=
  LeanPoo.Object.Dataflow.defineStrict "ResearchAmendment" do
    LeanPoo.Object.Dataflow.StrictBuilder.modifyInherited .sources
      (Option.map (· ++ [source research]))

def joinedPrototype : Except String
    (LeanPoo.Object.Dataflow.Instance LineageKey LineageValue) := do
  let hospital ← hospitalPrototype.mapError (fun _ => "invalid hospital prototype")
  let research ← researchAmendment.mapError (fun _ => "invalid research amendment")
  (hospital.defineStrictFrom "JoinedLineage" [research] do
    LeanPoo.Object.Dataflow.StrictBuilder.value .digest "joined-result").mapError
      (fun _ => "invalid joined prototype")

def joinedResult : DerivedArtifact :=
  (CedarPooSpec.Data.LineageProfile.artifact?
    (joinedPrototype.toOption.get (by native_decide))).get (by native_decide)

theorem joinedResultRetainsBothSources :
    joinedResult.sources = [source hospital, source research] := by
  native_decide

def studyDestination : Destination :=
  { resource := studyWorkspace, tenant := "hospital-a",
    acceptedOwners := [steward], acceptsRestricted := true }
def externalDestination : Destination :=
  { resource := externalWorkspace, tenant := "outside",
    acceptedOwners := [], acceptsRestricted := false }

private def fact (name : String) : Expr := .getAttr (.var .context) name
private def neg (body : Expr) : Expr := .unaryApp .not body
private def allFacts : Expr :=
  .and (fact "lineageAllowed")
    (.and (fact "approvalActive")
      (.and (fact "delegationActive")
        (.and (fact "budgetAvailable")
          (.and (fact "audienceAllowed")
            (.and (fact "payloadBound") (fact "auditReady"))))))

def broadPermit : Policy :=
  { id := "derived-publication", effect := .permit,
    principalScope := .principalScope (.eq agent),
    actionScope := .actionScope (.eq publish),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := .lit (.bool true) }] }
def boundedPermit : Policy :=
  { broadPermit with condition := [{ kind := .when, body := allFacts }] }
def gate (id name : String) : Veto :=
  { policyId := id, actionScope := .actionScope (.eq publish),
    denyWhen := neg (fact name) }
def lineageGate : Veto := gate "source-lineage" "lineageAllowed"
def approvalGate : Veto := gate "source-approvals" "approvalActive"
def delegationGate : Veto := gate "scoped-delegation" "delegationActive"
def cohortGate : Veto := gate "cumulative-cohort" "cohortSafe"
def budgetGate : Veto := gate "shared-release-budget" "budgetAvailable"
def audienceGate : Veto := gate "final-audience" "audienceAllowed"
def incidentGate : Veto :=
  { policyId := "publication-incident",
    actionScope := .actionScope (.eq publish),
    denyWhen := .lit (.bool true) }

def publicationModelResult : Except LeanPoo.C4.Error Model := do
  let base ← model.extend "DerivedPublicationBase" "ResultRelease"
    [.extend broadPermit]
  let lineage ← base.extend "SourceLineage" "DerivedPublicationBase"
    [lineageGate.edit .introduce]
  let approvals ← lineage.extend "SourceApprovals" "DerivedPublicationBase"
    [approvalGate.edit .introduce]
  let delegation ← approvals.extend "AgentDelegation" "DerivedPublicationBase"
    [delegationGate.edit .introduce]
  let cohort ← delegation.extend "CumulativeCohort" "DerivedPublicationBase"
    [cohortGate.edit .introduce]
  let budget ← cohort.extend "SharedDisclosureBudget" "DerivedPublicationBase"
    [budgetGate.edit .introduce]
  let audience ← budget.extend "FinalAudience" "DerivedPublicationBase"
    [audienceGate.edit .introduce]
  let governed ← audience.mix "DerivedPublicationGoverned"
    ["SourceLineage", "SourceApprovals", "AgentDelegation",
      "CumulativeCohort", "SharedDisclosureBudget", "FinalAudience"]
    [.overlay boundedPermit]
  let incident ← governed.extend "DerivedPublicationIncident"
    "DerivedPublicationGoverned" [incidentGate.edit .introduce]
  incident.extend "DerivedPublicationRecovered" "DerivedPublicationIncident"
    [incidentGate.edit .withdraw]
def publicationModel : Model := publicationModelResult.toOption.get (by native_decide)

/-- Retain checked policies for this exact model/schema, never request decisions. -/
def program : CedarPooSpec.Functional.Program publicationModel publicationSchema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard publicationModel publicationSchema
    (publicationModel.modules.map (·.name)) (by native_decide)

/-- Only composed roots may be used to prepare an external disclosure. The
    partial owner roots remain available for diagnostics and comparison. -/
inductive DeployableRoot where
  | governed | incident | recovered
  deriving DecidableEq

def DeployableRoot.name : DeployableRoot → String
  | .governed => "DerivedPublicationGoverned"
  | .incident => "DerivedPublicationIncident"
  | .recovered => "DerivedPublicationRecovered"

structure Effect where
  artifact : DerivedArtifact
  destination : Destination
  channel : String
  payloadDigest : String
  purpose : String
  recipients : List String
  candidateIds : List String := []
  selectionDelta : Option SelectionDelta := none
  deriving DecidableEq

structure State where
  epoch : Nat := 0
  approvalRevision : Nat := 0
  delegationRevision : Nat := 0
  policyRevision : Nat := 0
  audienceRevision : Nat := 0
  now : Nat := 1
  remaining : Nat := 1
  trustedSources : List SourceLabel := []
  observedDigest : String := ""
  observedSelection : Option SelectionDelta := none
  currentRecipients : List String := []
  recipientGrants : List (EntityUID × String) := []
  cohort : CumulativeDisclosure.Ledger := {}
  approvals : List ScopedApproval := []
  delegations : List CedarPooSpec.Governance.Personnel.Delegation := []
  auditReady : Bool := true
  audit : List String := []
  deriving DecidableEq

def approval (resource : EntityUID) : ScopedApproval :=
  { id := "study-one", approver := steward, actor := agent,
    operation := publish, purpose := "study-one", source := resource,
    target := studyWorkspace, revision := 0, expiresAt := 10 }
def delegation (resource : EntityUID) : CedarPooSpec.Governance.Personnel.Delegation :=
  { id := "study-one-agent", origin := steward, agent := agent,
    action := publish, asset := resource, destination := studyWorkspace,
    purpose := "study-one", revision := 0, expiresAt := 10 }
def initial : State :=
  { approvals := [approval hospital, approval research],
    delegations := [delegation hospital, delegation research],
    trustedSources := [source hospital, source research],
    currentRecipients := ["researcher-a"],
    recipientGrants := [(hospital, "researcher-a"), (research, "researcher-a")],
    observedDigest := joinedResult.digest }
def workspaceEffect : Effect :=
  { artifact := joinedResult, destination := studyDestination,
    channel := "workspace", payloadDigest := joinedResult.digest,
    purpose := "study-one", recipients := ["researcher-a"] }
def messageEffect : Effect :=
  { workspaceEffect with channel := "message" }
def externalEffect : Effect :=
  { workspaceEffect with destination := externalDestination }

def approvalsCover (state : State) (effect : Effect) : Bool :=
  effect.artifact.sources.all fun source =>
    state.approvals.any fun grant =>
      grant.approver == source.owner &&
      grant.applies agent publish effect.purpose source.resource
        effect.destination.resource state.approvalRevision state.now

def delegationsCover (state : State) (effect : Effect) : Bool :=
  effect.artifact.sources.all fun source =>
    state.delegations.any fun grant =>
      grant.applies source.owner agent publish source.resource
        effect.destination.resource effect.purpose state.delegationRevision state.now

def cohortSafe (state : State) (effect : Effect) : Bool :=
  state.cohort.admits effect.candidateIds

def audienceAllowed (state : State) (effect : Effect) : Bool :=
  !effect.recipients.isEmpty &&
    effect.recipients == state.currentRecipients &&
    effect.artifact.sources.all fun source =>
      effect.recipients.all fun recipient =>
        state.recipientGrants.contains (source.resource, recipient)

def selectionBound (state : State) (effect : Effect) : Bool :=
  let sink := if effect.channel == "workspace" then some SinkClass.sharedWorkspace
    else if effect.channel == "message" then some SinkClass.directMessage
    else none
  match sink with
  | none => false
  | some sink =>
      CedarPooSpec.AgenticAI.admitted
        { action := if effect.selectionDelta.isSome then .selectionMutation else .contentWrite
          sink, intendedSelection := effect.selectionDelta
          observedSelection := state.observedSelection
          candidateIds := effect.candidateIds
          outputBound := effect.payloadDigest == effect.artifact.digest &&
            effect.payloadDigest == state.observedDigest
          audienceAllowed := audienceAllowed state effect }

/-- The Host's grant-store change invalidates prepared authority even when
    the workspace member list stays the same. -/
def revokeRecipientGrant (state : State) (resource : EntityUID)
    (recipient : String) : State :=
  { state with
    recipientGrants := state.recipientGrants.filter
      (fun grant => grant != (resource, recipient)),
    audienceRevision := state.audienceRevision + 1,
    epoch := state.epoch + 1 }

def projectedRequest (state : State) (effect : Effect) : Request :=
  ⟨agent, publish, effect.destination.resource, Map.make [
    ("lineageAllowed", .prim (.bool
      (effect.artifact.sources == state.trustedSources &&
        effect.artifact.canFlowTo effect.destination))),
    ("approvalActive", .prim (.bool (approvalsCover state effect))),
    ("delegationActive", .prim (.bool (delegationsCover state effect))),
    ("cohortSafe", .prim (.bool (cohortSafe state effect))),
    ("budgetAvailable", .prim (.bool (state.remaining > 0))),
    ("audienceAllowed", .prim (.bool (audienceAllowed state effect))),
    ("payloadBound", .prim (.bool
      (selectionBound state effect))),
    ("auditReady", .prim (.bool state.auditReady))]⟩

def authorized
     (root : String) (state : State) (effect : Effect)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationModel CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationSchema :=
      CedarPooSpec.AgenticAI.LanguageModel.Disclosure.program) : Bool :=
  match programContext.authorize root [projectedRequest state effect] publicationEntities with
  | .error _ => false
  | .ok receipt => receipt.allowed

structure Ticket where
  root : DeployableRoot
  epoch : Nat
  approvalRevision : Nat
  delegationRevision : Nat
  policyRevision : Nat
  audienceRevision : Nat
  effect : Effect
  deriving DecidableEq

def prepare
     (root : DeployableRoot) (state : State) (effect : Effect)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationModel CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationSchema :=
      CedarPooSpec.AgenticAI.LanguageModel.Disclosure.program) : Option Ticket :=
  if effect.channel.isEmpty || !(authorized (programContext := programContext)) root.name state effect then none
  else some ⟨root, state.epoch, state.approvalRevision, state.delegationRevision,
    state.policyRevision, state.audienceRevision, effect⟩

/-- A finite atomic-state model. A real Host must persist the shared ledger
    and audit before making either channel's external effect visible. -/
def redeem
     (state : State) (ticket : Ticket) (effect : Effect)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationModel CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationSchema :=
      CedarPooSpec.AgenticAI.LanguageModel.Disclosure.program) : Option State :=
  if ticket.epoch != state.epoch ||
      ticket.approvalRevision != state.approvalRevision ||
      ticket.delegationRevision != state.delegationRevision ||
      ticket.policyRevision != state.policyRevision ||
      ticket.audienceRevision != state.audienceRevision ||
      ticket.effect != effect || !(authorized (programContext := programContext)) ticket.root.name state effect then none
  else
    match state.cohort.record effect.candidateIds with
    | none => none
    | some cohort =>
        let next := { state with epoch := state.epoch + 1 }
        let next := { next with remaining := state.remaining - 1 }
        let next := { next with cohort }
        let next := { next with audit := state.audit ++ [effect.payloadDigest] }
        some next

def release
     (root : DeployableRoot) (state : State) (effect : Effect)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationModel CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationSchema :=
      CedarPooSpec.AgenticAI.LanguageModel.Disclosure.program) : Option State := do
  let ticket ← (prepare (programContext := programContext)) root state effect
  (redeem (programContext := programContext)) state ticket effect

theorem validWorkspaceRelease :
    (release .governed initial workspaceEffect).isSome = true := by
  native_decide

theorem crossChannelUsesOneBudget :
    ((release .governed initial workspaceEffect).bind
      fun next => release .governed next messageEffect) = none := by
  native_decide

theorem externalDestinationDenied :
    prepare .governed initial externalEffect = none := by
  native_decide

theorem changedOrUnapprovedAudienceDenied :
    prepare .governed initial
      { workspaceEffect with recipients := ["researcher-a", "outsider"] } = none ∧
    prepare .governed
      { initial with currentRecipients := ["researcher-a", "outsider"] }
      { workspaceEffect with recipients := ["researcher-a", "outsider"] } = none ∧
    prepare .governed
      { initial with recipientGrants := [(hospital, "researcher-a")] }
      workspaceEffect = none ∧
    ((prepare .governed initial workspaceEffect).bind fun ticket =>
      redeem { initial with audienceRevision := 1, currentRecipients := ["researcher-a", "outsider"] }
        ticket workspaceEffect) = none := by
  native_decide

theorem revokedRecipientGrantDeniesPreparedAndFreshTicket :
    ((prepare .governed initial workspaceEffect).bind fun ticket =>
      redeem (revokeRecipientGrant initial research "researcher-a")
        ticket workspaceEffect) = none ∧
    prepare .governed
      (revokeRecipientGrant initial research "researcher-a") workspaceEffect = none := by
  native_decide

theorem incompleteLineageOrApprovalDenied :
    prepare .governed initial
      { workspaceEffect with artifact := { joinedResult with sources := [] } } = none ∧
    prepare .governed initial
      { workspaceEffect with artifact := { joinedResult with sources := [source hospital] } } = none ∧
    prepare .governed
      { initial with approvals := [approval hospital] } workspaceEffect = none := by
  native_decide

theorem staleTicketAndChangedChannelDenied :
    ((prepare .governed initial workspaceEffect).bind
      fun ticket => redeem { initial with approvalRevision := 1 } ticket workspaceEffect) = none ∧
    ((prepare .governed initial workspaceEffect).bind
      fun ticket => redeem initial ticket messageEffect) = none := by
  native_decide

theorem revokedOrIncompleteDelegationDenied :
    prepare .governed { initial with delegationRevision := 1 } workspaceEffect = none ∧
    prepare .governed
      { initial with delegations := [delegation hospital] } workspaceEffect = none ∧
    ((prepare .governed initial workspaceEffect).bind fun ticket =>
      redeem { initial with delegationRevision := 1 } ticket workspaceEffect) = none := by
  native_decide

theorem unobservedPayloadDenied :
    prepare .governed initial
      { workspaceEffect with payloadDigest := "substituted-output" } = none := by
  native_decide

def cohortInitial : State :=
  { initial with remaining := 2, cohort := { possibleIds := ["p1", "p2", "p3", "p4", "p5", "p6"], minimum := 3 }, observedDigest := "cohort-first" }

def firstCohort : Effect :=
  { workspaceEffect with
    artifact := { joinedResult with digest := "cohort-first" },
    payloadDigest := "cohort-first",
    candidateIds := ["p1", "p2", "p3", "p4"] }

def secondCohort : Effect :=
  { messageEffect with
    artifact := { joinedResult with digest := "cohort-second" },
    payloadDigest := "cohort-second",
    candidateIds := ["p3", "p4", "p5", "p6"] }

def cohortAfterFirst
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationModel CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationSchema :=
      CedarPooSpec.AgenticAI.LanguageModel.Disclosure.program) : Option State := do
  let next ← (release (programContext := programContext)) .governed cohortInitial firstCohort
  some { next with observedDigest := "cohort-second" }

/-- Each release has four candidate IDs in isolation, but their intersection
    has only two. The second disclosure is rejected despite remaining budget. -/
theorem multiTurnCohortCollapseDenied :
    (release .governed cohortInitial firstCohort).isSome = true ∧
    (release .governed
      { cohortInitial with observedDigest := "cohort-second" } secondCohort).isSome = true ∧
    (cohortAfterFirst.bind fun state => release .governed state secondCohort) = none := by
  native_decide

def firstSelection : SelectionDelta :=
  { before := ["p1", "p2", "p3", "p4", "p5", "p6"],
    after := ["p1", "p2", "p3", "p4"] }
def secondSelection : SelectionDelta :=
  { before := ["p1", "p2", "p3", "p4", "p5", "p6"],
    after := ["p3", "p4", "p5", "p6"] }
def selectionInitial : State :=
  { { cohortInitial with observedDigest := "selection-first" } with
    observedSelection := some firstSelection }
def selectionFirst : Effect :=
  { firstCohort with
    artifact := { joinedResult with digest := "selection-first" },
    payloadDigest := "selection-first", selectionDelta := some firstSelection }
def selectionSecond : Effect :=
  { secondCohort with
    artifact := { joinedResult with digest := "selection-second" },
    payloadDigest := "selection-second", selectionDelta := some secondSelection }
def selectionAfterFirst
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationModel CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationSchema :=
      CedarPooSpec.AgenticAI.LanguageModel.Disclosure.program) : Option State := do
  let next ← (release (programContext := programContext)) .governed selectionInitial selectionFirst
  some { { next with observedDigest := "selection-second" } with
    observedSelection := some secondSelection }

/-- A selective deletion exposes the survivor set even when it writes no
    sensitive text. It consumes the same shared cohort ledger as a write. -/
theorem selectiveDeletionIsMediated :
    (release .governed selectionInitial selectionFirst).isSome = true ∧
    prepare .governed { selectionInitial with observedSelection := none }
      selectionFirst = none ∧
    prepare .governed selectionInitial
      { selectionFirst with candidateIds := ["p1", "p2", "p3"] } = none ∧
    (selectionAfterFirst.bind fun state =>
      release .governed state selectionSecond) = none := by
  native_decide

theorem incidentAndRecovery :
    prepare .incident initial workspaceEffect = none ∧
    (release .recovered initial workspaceEffect).isSome = true := by
  native_decide

/-- Fixed replay inputs carry actual transition equalities. Constructing their
semantic states needs no repeated policy preparation during module loading. -/
private def cohortAfterFirstState : State :=
  { cohortInitial with
    epoch := cohortInitial.epoch + 1
    remaining := cohortInitial.remaining - 1
    cohort := (cohortInitial.cohort.record firstCohort.candidateIds).get (by native_decide)
    audit := cohortInitial.audit ++ [firstCohort.payloadDigest]
    observedDigest := "cohort-second" }

private def selectionAfterFirstState : State :=
  { selectionInitial with
    epoch := selectionInitial.epoch + 1
    remaining := selectionInitial.remaining - 1
    cohort := (selectionInitial.cohort.record selectionFirst.candidateIds).get (by native_decide)
    audit := selectionInitial.audit ++ [selectionFirst.payloadDigest]
    observedDigest := "selection-second"
    observedSelection := some secondSelection }

theorem cohortFixture_evaluated : cohortAfterFirst = some cohortAfterFirstState := by native_decide
theorem selectionFixture_evaluated : selectionAfterFirst = some selectionAfterFirstState := by native_decide

def cases : List (String × String × State × Effect × Decision) := [
  ("source-base-allows-external", "DerivedPublicationBase", initial, externalEffect, .allow),
  ("source-governed-study", "DerivedPublicationGoverned", initial, workspaceEffect, .allow),
  ("source-governed-external", "DerivedPublicationGoverned", initial, externalEffect, .deny),
  ("source-missing-owner", "DerivedPublicationGoverned",
    { initial with approvals := [approval hospital] }, workspaceEffect, .deny),
  ("source-delegation-revoked", "DerivedPublicationGoverned",
    { initial with delegationRevision := 1 }, workspaceEffect, .deny),
  ("source-delegation-missing", "DerivedPublicationGoverned",
    { initial with delegations := [delegation hospital] }, workspaceEffect, .deny),
  ("source-audience-expanded", "DerivedPublicationGoverned",
    { initial with currentRecipients := ["researcher-a", "outsider"] },
    { workspaceEffect with recipients := ["researcher-a", "outsider"] }, .deny),
  ("source-audience-grant-missing", "DerivedPublicationGoverned",
    { initial with recipientGrants := [(hospital, "researcher-a")] },
    workspaceEffect, .deny),
  ("source-cohort-first", "DerivedPublicationGoverned", cohortInitial, firstCohort, .allow),
  ("source-cohort-second-alone", "DerivedPublicationGoverned",
    { cohortInitial with observedDigest := "cohort-second" }, secondCohort, .allow),
  ("source-cohort-second-after-first", "DerivedPublicationGoverned",
    cohortAfterFirstState, secondCohort, .deny),
  ("source-selection-survivors", "DerivedPublicationGoverned",
    selectionInitial, selectionFirst, .allow),
  ("source-selection-unobserved", "DerivedPublicationGoverned",
    { selectionInitial with observedSelection := none }, selectionFirst, .deny),
  ("source-selection-candidates-changed", "DerivedPublicationGoverned",
    selectionInitial,
    { selectionFirst with candidateIds := ["p1", "p2", "p3"] }, .deny),
  ("source-selection-second-after-first", "DerivedPublicationGoverned",
    selectionAfterFirstState, selectionSecond, .deny),
  ("source-dropped-label", "DerivedPublicationGoverned", initial,
    { workspaceEffect with artifact := { joinedResult with sources := [source hospital] } }, .deny),
  ("source-substituted-output", "DerivedPublicationGoverned", initial,
    { workspaceEffect with payloadDigest := "substituted-output" }, .deny),
  ("source-budget-exhausted", "DerivedPublicationGoverned",
    { initial with remaining := 0 }, messageEffect, .deny),
  ("source-incident", "DerivedPublicationIncident", initial, workspaceEffect, .deny),
  ("source-recovered", "DerivedPublicationRecovered", initial, workspaceEffect, .allow)]

def casesConform
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationModel CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationSchema :=
      CedarPooSpec.AgenticAI.LanguageModel.Disclosure.program) : Bool := cases.all fun (_, root, state, effect, expected) =>
  match programContext.authorize root [projectedRequest state effect] publicationEntities with
  | .error _ => false
  | .ok receipt => receipt.responses.all fun answer =>
      answer.decision == expected && answer.erroringPolicies.isEmpty

theorem casesConformFully : casesConform = true := by native_decide

end CedarPooSpec.AgenticAI.LanguageModel.Disclosure
