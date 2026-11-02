import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Cloud.Pipeline.ReleaseBoundary
import CedarPooSpec.Cloud.Pipeline.Evidence
import CedarPooSpec.Cloud.Pipeline.SourceControlBoundary
import CedarPooSpec.Cloud.Pipeline.SourceProfile

/-!
Synthetic pipeline release based on Google Cloud Threat Intelligence's 2026
cross-stage hardening guidance. No real Google, GitHub, or registry state is
read here; the Host must attest the projected facts and execute the effect.
-/

namespace CedarPooSpec.Cloud.Pipeline.GoogleThreatCase

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Cloud.Pipeline CedarPooSpec.Governance

def builderType : EntityType := ⟨"Builder", []⟩
def artifactType : EntityType := ⟨"Artifact", []⟩
def provenanceType : EntityType := ⟨"Provenance", []⟩
def sourceChangeType : EntityType := ⟨"SourceChange", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def builder : EntityUID := ⟨builderType, "release-bot"⟩
def candidate : EntityUID := ⟨artifactType, "service-release"⟩
def unaffected : EntityUID := ⟨artifactType, "independent-release"⟩
def promote : EntityUID := ⟨actionType, "promote"⟩
def candidateProvenance : EntityUID := ⟨provenanceType, "candidate-build"⟩
def independentProvenance : EntityUID := ⟨provenanceType, "independent-build"⟩
def substitutedSource : EntityUID := ⟨provenanceType, "other-source"⟩
def substitutedWorkflow : EntityUID := ⟨provenanceType, "other-workflow"⟩
def substitutedAudience : EntityUID := ⟨provenanceType, "other-audience"⟩
def substitutedBuilder : EntityUID := ⟨provenanceType, "other-builder"⟩
def substitutedSubject : EntityUID := ⟨provenanceType, "other-subject"⟩
def reviewedChange : EntityUID := ⟨sourceChangeType, "reviewed-candidate"⟩
def independentChange : EntityUID := ⟨sourceChangeType, "reviewed-independent"⟩
def otherCommitChange : EntityUID := ⟨sourceChangeType, "other-commit"⟩
def otherRepositoryChange : EntityUID := ⟨sourceChangeType, "other-repository"⟩
def selfReviewedChange : EntityUID := ⟨sourceChangeType, "self-review"⟩
def failedChecksChange : EntityUID := ⟨sourceChangeType, "failed-checks"⟩
def bypassedChange : EntityUID := ⟨sourceChangeType, "bypass"⟩
def rewrittenChange : EntityUID := ⟨sourceChangeType, "rewritten-history"⟩
def staleReviewChange : EntityUID := ⟨sourceChangeType, "stale-review"⟩
def otherBranchChange : EntityUID := ⟨sourceChangeType, "other-branch"⟩
def agentAuthoredChange : EntityUID := ⟨sourceChangeType, "agent-authored-human-reviewed"⟩
def agentApprovedChange : EntityUID := ⟨sourceChangeType, "agent-approved"⟩
def canaryChange : EntityUID := ⟨sourceChangeType, "canary-branch"⟩

def fields : List String := ProvenanceClaim.fields

def signals : List String :=
  ["reviewed", "protectedRef", "lockVerified",
    "dependenciesQuarantined", "actionsPinned", "ephemeralRunner",
    "cacheIsolated", "untrustedPrBlocked", "signatureVerified",
    "provenanceVerified", "incidentActive"]

def contextType : RecordType := Map.make
  (fields.map (fun key => (key, .required .string)) ++
    signals.map (fun key => (key, .required (.bool .anyBool))) ++
    [("provenance", .required (.entity provenanceType)),
      ("sourceChange", .required (.entity sourceChangeType)),
      ("sourceChangeVerified", .required (.bool .anyBool)),
      ("sourceIdentityVerified", .required (.bool .anyBool)),
      ("currentSourceEpoch", .required .int)])

def artifactEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make
    (fields.map (fun key => (key, .required .string)) ++
      [("affected", .required (.bool .anyBool))]), none⟩

def provenanceEntry : EntitySchemaEntry := ProvenanceClaim.schemaEntry

def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [builderType], Set.make [artifactType], Set.empty, contextType⟩

def schema : Schema :=
  ⟨Map.make [(builderType, .standard ⟨Set.empty, Map.empty, none⟩),
    (artifactType, artifactEntry), (provenanceType, provenanceEntry),
    (sourceChangeType, SourceChangeClaim.schemaEntry)],
    Map.make [(promote, actionEntry)]⟩

structure Target extends ProvenanceClaim where
  sourceRepository : String := "repo-a"
  sourceCommit : String := "commit-a"
  workflow : String := "release-workflow"
  lockDigest : String := "lock-a"
  oidcAudience : String := "registry-release"
  buildType : String := "trusted-build"
  artifactDigest : String := "sha256:candidate"
  builderIdentity : String := "trusted-builder"
  affected : Bool := true

def targetValues (target : Target) : List (String × Value) :=
  target.toProvenanceClaim.values

def artifactData (target : Target) : EntityData :=
  { attrs := Map.make (targetValues target ++
      [("affected", .prim (.bool target.affected))]),
    ancestors := Set.empty, tags := Map.empty }

def provenanceData (target : Target) : EntityData :=
  target.toProvenanceClaim.entityData

def emptyData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }

def acceptedChange : SourceChangeClaim :=
  { repository := "repo-a", commit := "commit-a", branch := "main",
    author := "developer-a", reviewer := "reviewer-b", reviewerHuman := true,
    policyEpoch := 7,
    reviewApproved := true, checksPassed := true, branchProtected := true,
    bypassUsed := false, historyRewritten := false }

def agentAuthoredClaim : SourceChangeClaim :=
  { acceptedChange with author := "coding-agent" }

def agentApprovedClaim : SourceChangeClaim :=
  { { agentAuthoredClaim with reviewer := "review-bot" } with
    reviewerHuman := false }

def entities : Entities := Map.make
  [(builder, emptyData),
   (candidate, artifactData {}),
   (unaffected, artifactData
     { sourceCommit := "commit-b", lockDigest := "lock-b",
       artifactDigest := "sha256:independent", affected := false }),
   (candidateProvenance, provenanceData {}),
   (independentProvenance, provenanceData
     { sourceCommit := "commit-b", lockDigest := "lock-b",
       artifactDigest := "sha256:independent" }),
   (substitutedSource, provenanceData { sourceCommit := "other-commit" }),
   (substitutedWorkflow, provenanceData { workflow := "other-workflow" }),
   (substitutedAudience, provenanceData { oidcAudience := "other-audience" }),
   (substitutedBuilder, provenanceData { builderIdentity := "other-builder" }),
   (substitutedSubject, provenanceData { artifactDigest := "sha256:other" }),
   (reviewedChange, acceptedChange.entityData),
   (independentChange, { acceptedChange with commit := "commit-b" }.entityData),
   (otherCommitChange, { acceptedChange with commit := "other-commit" }.entityData),
   (otherRepositoryChange, { acceptedChange with repository := "other-repository" }.entityData),
   (selfReviewedChange, { acceptedChange with reviewer := "developer-a" }.entityData),
   (failedChecksChange, { acceptedChange with checksPassed := false }.entityData),
   (bypassedChange, { acceptedChange with bypassUsed := true }.entityData),
   (rewrittenChange, { acceptedChange with historyRewritten := true }.entityData),
   (staleReviewChange, { acceptedChange with policyEpoch := 6 }.entityData),
   (otherBranchChange, { acceptedChange with branch := "feature" }.entityData),
   (agentAuthoredChange, agentAuthoredClaim.entityData),
   (agentApprovedChange, agentApprovedClaim.entityData),
   (canaryChange, { acceptedChange with branch := "release-candidate" }.entityData),
   (promote, actionSchemaEntryToEntityData actionEntry)]

structure Facts extends Target where
  provenance : EntityUID := candidateProvenance
  sourceChange : EntityUID := reviewedChange
  sourceChangeVerified : Bool := true
  sourceIdentityVerified : Bool := true
  currentSourceEpoch : Int64 := 7
  reviewed : Bool := true
  protectedRef : Bool := true
  lockVerified : Bool := true
  dependenciesQuarantined : Bool := true
  actionsPinned : Bool := true
  ephemeralRunner : Bool := true
  cacheIsolated : Bool := true
  untrustedPrBlocked : Bool := true
  signatureVerified : Bool := true
  provenanceVerified : Bool := true
  incidentActive : Bool := false

def context (facts : Facts) : Map String Value := Map.make
  (targetValues facts.toTarget ++
   [("reviewed", .prim (.bool facts.reviewed)),
    ("protectedRef", .prim (.bool facts.protectedRef)),
    ("lockVerified", .prim (.bool facts.lockVerified)),
    ("dependenciesQuarantined", .prim (.bool facts.dependenciesQuarantined)),
    ("actionsPinned", .prim (.bool facts.actionsPinned)),
    ("ephemeralRunner", .prim (.bool facts.ephemeralRunner)),
    ("cacheIsolated", .prim (.bool facts.cacheIsolated)),
    ("untrustedPrBlocked", .prim (.bool facts.untrustedPrBlocked)),
    ("signatureVerified", .prim (.bool facts.signatureVerified)),
    ("provenanceVerified", .prim (.bool facts.provenanceVerified)),
    ("incidentActive", .prim (.bool facts.incidentActive)),
    ("provenance", .prim (.entityUID facts.provenance)),
    ("sourceChange", .prim (.entityUID facts.sourceChange)),
    ("sourceChangeVerified", .prim (.bool facts.sourceChangeVerified)),
    ("sourceIdentityVerified", .prim (.bool facts.sourceIdentityVerified)),
    ("currentSourceEpoch", .prim (.int facts.currentSourceEpoch))])

def request (resource : EntityUID) (facts : Facts) : Request :=
  ⟨builder, promote, resource, context facts⟩

def grant : Policy :=
  { id := "candidate-promotion", effect := .permit,
    principalScope := .principalScope (.eq builder),
    actionScope := .actionScope (.eq promote),
    resourceScope := .resourceScope (.is artifactType), condition := [] }

def boundary (stage : Stage) : ReleaseBoundary :=
  { policyId := s!"pipeline-{stage.name}"
    actionScope := .actionScope (.eq promote)
    resourceScope := .resourceScope (.is artifactType)
    stage }

def sourceControl : SourceControlBoundary :=
  { policyId := "pipeline-source-control",
    actionScope := .actionScope (.eq promote),
    resourceScope := .resourceScope (.is artifactType),
    protectedBranch := "main" }

def productionProfile : SourceProfile.Object :=
  (SourceProfile.define "ProductionSource" sourceControl).toOption.get
    (by native_decide)

def canaryProfile : SourceProfile.Object :=
  (SourceProfile.onBranch productionProfile "CanarySource" "release-candidate")
    |>.toOption.get (by native_decide)

def productionControl : SourceControlBoundary :=
  (SourceProfile.control? productionProfile).get (by native_decide)

def canaryControl : SourceControlBoundary :=
  (SourceProfile.control? canaryProfile).get (by native_decide)

def incident : Veto :=
  { policyId := "affected-artifact-quarantine",
    actionScope := .actionScope (.eq promote),
    resourceScope := .resourceScope (.is artifactType),
    denyWhen := .and (.getAttr (.var .resource) "affected")
      (.getAttr (.var .context) "incidentActive") }

/-- Independent stage owners become one C4 policy object; later incident and
    recovery revisions leave every unaffected stage owner reusable. -/
def modelResult : Except LeanPoo.Object.CombineError Model := do
  let base ← (Model.define "Base" [.extend grant]).mapError .c4
  let source ← (Model.define "Source" [(boundary .source).veto.edit .introduce]).mapError .c4
  let review ← (Model.define "SourceControl"
    [productionControl.veto.edit .introduce]).mapError .c4
  let dependency ← (Model.define "Dependencies"
    [(boundary .dependencies).veto.edit .introduce]).mapError .c4
  let runner ← (Model.define "Runner" [(boundary .runner).veto.edit .introduce]).mapError .c4
  let artifact ← (Model.define "Artifact" [(boundary .artifact).veto.edit .introduce]).mapError .c4
  let provenance ← (Model.define "Provenance"
    [(boundary .provenance).veto.edit .introduce]).mapError .c4
  let sourcePrecheck ← base.combine "Base" [(source, "Source")] "SourcePrecheck"
  let sourceBound ← sourcePrecheck.combine "SourcePrecheck"
    [(review, "SourceControl")] "SourceBound"
  let dependencyBound ← sourceBound.combine "SourceBound"
    [(dependency, "Dependencies")] "DependencyBound"
  let runnerBound ← dependencyBound.combine "DependencyBound"
    [(runner, "Runner")] "RunnerBound"
  let artifactBound ← runnerBound.combine "RunnerBound"
    [(artifact, "Artifact")] "ArtifactBound"
  let releaseReady ← artifactBound.combine "ArtifactBound"
    [(provenance, "Provenance")] "ReleaseReady"
  let quarantined ← (releaseReady.extend "Quarantined" "ReleaseReady"
    [incident.edit .introduce]).mapError .c4
  let recovered ← (quarantined.extend "Recovered" "Quarantined"
    [incident.edit .withdraw]).mapError .c4
  (recovered.extend "CanaryRelease" "ReleaseReady"
    [canaryControl.veto.edit .revise]).mapError .c4

def model : Model := modelResult.toOption.get (by native_decide)

/-- Prepared against this exact model/schema; requests and entities remain current. -/
def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard model schema
    (model.modules.map (·.name)) (by native_decide)

def allowed
     (root : String) (resource : EntityUID) (facts : Facts)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.Pipeline.GoogleThreatCase.model CedarPooSpec.Cloud.Pipeline.GoogleThreatCase.schema :=
      CedarPooSpec.Cloud.Pipeline.GoogleThreatCase.program) : Bool :=
  match programContext.authorize root [request resource facts] entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

def independentFacts : Facts :=
  { sourceCommit := "commit-b", lockDigest := "lock-b",
    artifactDigest := "sha256:independent", affected := false,
    provenance := independentProvenance, sourceChange := independentChange }

def cases : List (String × String × EntityUID × Facts × Bool) := [
  ("base-accepts-wrong-commit", "Base", candidate,
    { sourceCommit := "other-commit" }, true),
  ("source-blocks-wrong-commit", "SourceBound", candidate,
    { sourceCommit := "other-commit" }, false),
  ("source-blocks-unreviewed-change", "SourceBound", candidate,
    { reviewed := false }, false),
  ("source-blocks-other-workflow", "SourceBound", candidate,
    { workflow := "untrusted-workflow" }, false),
  ("source-blocks-other-repository", "SourceBound", candidate,
    { sourceRepository := "other-repository" }, false),
  ("source-precheck-misses-other-review-commit", "SourcePrecheck", candidate,
    { sourceChange := otherCommitChange }, true),
  ("source-control-binds-reviewed-commit", "SourceBound", candidate,
    { sourceChange := otherCommitChange }, false),
  ("source-control-binds-repository", "SourceBound", candidate,
    { sourceChange := otherRepositoryChange }, false),
  ("source-control-rejects-self-review", "SourceBound", candidate,
    { sourceChange := selfReviewedChange }, false),
  ("source-control-rejects-failed-checks", "SourceBound", candidate,
    { sourceChange := failedChecksChange }, false),
  ("source-control-rejects-bypass", "SourceBound", candidate,
    { sourceChange := bypassedChange }, false),
  ("source-control-rejects-history-rewrite", "SourceBound", candidate,
    { sourceChange := rewrittenChange }, false),
  ("source-control-rejects-stale-ruleset", "SourceBound", candidate,
    { sourceChange := staleReviewChange }, false),
  ("source-control-rejects-other-branch", "SourceBound", candidate,
    { sourceChange := otherBranchChange }, false),
  ("source-control-rejects-unverified-review", "SourceBound", candidate,
    { sourceChangeVerified := false }, false),
  ("source-control-rejects-unverified-identity", "SourceBound", candidate,
    { sourceIdentityVerified := false }, false),
  ("source-control-accepts-agent-code-human-review", "SourceBound", candidate,
    { sourceChange := agentAuthoredChange }, true),
  ("source-control-rejects-agent-only-review", "SourceBound", candidate,
    { sourceChange := agentApprovedChange }, false),
  ("production-rejects-canary-source", "ReleaseReady", candidate,
    { sourceChange := canaryChange }, false),
  ("canary-accepts-canary-source", "CanaryRelease", candidate,
    { sourceChange := canaryChange }, true),
  ("canary-rejects-production-source", "CanaryRelease", candidate,
    {}, false),
  ("canary-preserves-provenance", "CanaryRelease", candidate,
    { sourceChange := canaryChange, provenanceVerified := false }, false),
  ("source-alone-misses-poisoned-package", "SourceBound", candidate,
    { dependenciesQuarantined := false }, true),
  ("dependency-blocks-poisoned-package", "DependencyBound", candidate,
    { dependenciesQuarantined := false }, false),
  ("dependency-blocks-mutable-action", "DependencyBound", candidate,
    { actionsPinned := false }, false),
  ("dependency-alone-misses-cache-poison", "DependencyBound", candidate,
    { cacheIsolated := false }, true),
  ("runner-blocks-cache-poison", "RunnerBound", candidate,
    { cacheIsolated := false }, false),
  ("runner-blocks-untrusted-pr", "RunnerBound", candidate,
    { untrustedPrBlocked := false }, false),
  ("runner-blocks-wrong-audience", "RunnerBound", candidate,
    { oidcAudience := "other-registry" }, false),
  ("runner-alone-misses-false-provenance", "RunnerBound", candidate,
    { provenanceVerified := false }, true),
  ("artifact-alone-misses-false-provenance", "ArtifactBound", candidate,
    { provenanceVerified := false }, true),
  ("provenance-blocks-unverified-claim", "ReleaseReady", candidate,
    { provenanceVerified := false }, false),
  ("artifact-alone-misses-source-substitution", "ArtifactBound", candidate,
    { provenance := substitutedSource }, true),
  ("provenance-blocks-source-substitution", "ReleaseReady", candidate,
    { provenance := substitutedSource }, false),
  ("provenance-blocks-workflow-substitution", "ReleaseReady", candidate,
    { provenance := substitutedWorkflow }, false),
  ("provenance-blocks-audience-substitution", "ReleaseReady", candidate,
    { provenance := substitutedAudience }, false),
  ("provenance-blocks-builder-substitution", "ReleaseReady", candidate,
    { provenance := substitutedBuilder }, false),
  ("provenance-blocks-subject-substitution", "ReleaseReady", candidate,
    { provenance := substitutedSubject }, false),
  ("artifact-blocks-unsigned-output", "ReleaseReady", candidate,
    { signatureVerified := false }, false),
  ("artifact-blocks-replaced-digest", "ReleaseReady", candidate,
    { artifactDigest := "sha256:replaced" }, false),
  ("artifact-blocks-wrong-builder", "ReleaseReady", candidate,
    { builderIdentity := "unexpected-builder" }, false),
  ("artifact-blocks-wrong-build-type", "ReleaseReady", candidate,
    { buildType := "untrusted-build" }, false),
  ("ready-promotion", "ReleaseReady", candidate, {}, true),
  ("incident-quarantines-affected", "Quarantined", candidate,
    { incidentActive := true }, false),
  ("incident-preserves-independent", "Quarantined", unaffected,
    { independentFacts with incidentActive := true }, true),
  ("recovery-restores-affected", "Recovered", candidate,
    { incidentActive := true }, true),
  ("recovery-keeps-cache-isolation", "Recovered", candidate,
    { cacheIsolated := false }, false)]

end CedarPooSpec.Cloud.Pipeline.GoogleThreatCase
