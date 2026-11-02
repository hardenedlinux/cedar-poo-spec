import CedarPooSpec.Functional.Capabilities
import Examples.Cloud.Pipeline.GoogleThreatCase
import CedarPooSpec.Cloud.Pipeline.DeploymentBoundary

/-! Synthetic Google-style artifact deployment. The first decision qualifies
the build; the second admits the exact digest at the deployment boundary. -/

namespace CedarPooSpec.Cloud.Pipeline.DeploymentCase

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Cloud.Pipeline CedarPooSpec.Governance

def attestationType : EntityType := ⟨"Attestation", []⟩
def releaseReceiptType : EntityType := ⟨"ReleaseReceipt", []⟩
def deploymentServiceType : EntityType := ⟨"DeploymentService", []⟩
def deploy : EntityUID := ⟨GoogleThreatCase.actionType, "deploy"⟩
def service : EntityUID := ⟨deploymentServiceType, "deployment-controller"⟩
def correctAttestation : EntityUID := ⟨attestationType, "release-approval"⟩
def otherSubject : EntityUID := ⟨attestationType, "other-subject"⟩
def otherAttestor : EntityUID := ⟨attestationType, "other-attestor"⟩
def currentRelease : EntityUID := ⟨releaseReceiptType, "current-release"⟩
def otherReleaseDigest : EntityUID := ⟨releaseReceiptType, "other-digest"⟩
def otherReleaseRoot : EntityUID := ⟨releaseReceiptType, "other-root"⟩
def staleRelease : EntityUID := ⟨releaseReceiptType, "stale-release"⟩

def approvedAttestation : AttestationClaim :=
  { subjectDigest := "sha256:candidate", attestor := "secure-build" }

def acceptedRelease : ReleaseReceiptClaim :=
  { artifactDigest := "sha256:candidate", sourceCommit := "commit-a",
    policyRoot := "ReleaseReady", epoch := 7 }

def deployContext : RecordType := Map.make [
  ("attestation", .required (.entity attestationType)),
  ("deploymentDigest", .required .string),
  ("releaseReceipt", .required (.entity releaseReceiptType)),
  ("releaseReceiptVerified", .required (.bool .anyBool)),
  ("currentEpoch", .required .int),
  ("attestationVerified", .required (.bool .anyBool)),
  ("immutableReference", .required (.bool .anyBool)),
  ("policyEnforced", .required (.bool .anyBool)),
  ("incidentActive", .required (.bool .anyBool))]

def deployAction : ActionSchemaEntry :=
  ⟨Set.make [deploymentServiceType], Set.make [GoogleThreatCase.artifactType],
    Set.empty, deployContext⟩

def schema : Schema :=
  ⟨Map.make (GoogleThreatCase.schema.ets.toList ++ [
      (attestationType, AttestationClaim.schemaEntry),
      (releaseReceiptType, ReleaseReceiptClaim.schemaEntry),
      (deploymentServiceType, .standard ⟨Set.empty, Map.empty, none⟩)]),
   Map.make (GoogleThreatCase.schema.acts.toList ++ [(deploy, deployAction)])⟩

def entities : Entities := Map.make (GoogleThreatCase.entities.toList ++ [
  (service, GoogleThreatCase.emptyData),
  (correctAttestation, approvedAttestation.entityData),
  (otherSubject, { approvedAttestation with subjectDigest := "sha256:other" }.entityData),
  (otherAttestor, { approvedAttestation with attestor := "untrusted-approval" }.entityData),
  (currentRelease, acceptedRelease.entityData),
  (otherReleaseDigest, { acceptedRelease with artifactDigest := "sha256:other" }.entityData),
  (otherReleaseRoot, { acceptedRelease with policyRoot := "OtherRoot" }.entityData),
  (staleRelease, { acceptedRelease with epoch := 6 }.entityData),
  (deploy, actionSchemaEntryToEntityData deployAction)])

def grant : Policy :=
  { id := "deploy-candidate", effect := .permit,
    principalScope := .principalScope (.eq service),
    actionScope := .actionScope (.eq deploy),
    resourceScope := .resourceScope (.eq GoogleThreatCase.candidate),
    condition := [] }

def boundary : DeploymentBoundary :=
  { policyId := "deploy-digest-attestation",
    actionScope := .actionScope (.eq deploy),
    resourceScope := .resourceScope (.is GoogleThreatCase.artifactType),
    requiredAttestor := "secure-build",
    requiredReleaseRoot := "ReleaseReady" }

def deploymentIncident : Veto :=
  { policyId := "deploy-affected-artifact-quarantine",
    actionScope := .actionScope (.eq deploy),
    resourceScope := .resourceScope (.is GoogleThreatCase.artifactType),
    denyWhen := .and (.getAttr (.var .resource) "affected")
      (.getAttr (.var .context) "incidentActive") }

/-- A deployment customer selects the complete pipeline and adds two owned
    deployment slots. Its incident revision reuses the same attestation owner. -/
def modelResult : Except LeanPoo.Object.CombineError Model := do
  let permit ← (Model.define "DeployPermit" [.extend grant]).mapError .c4
  let attestation ← (Model.define "DeployAttestation"
    [boundary.veto.edit .introduce]).mapError .c4
  let deployment ← permit.combine "DeployPermit"
    [(attestation, "DeployAttestation")] "DeploymentControls"
  let ready ← GoogleThreatCase.model.combine "ReleaseReady"
    [(deployment, "DeploymentControls")] "DeploymentReady"
  let incident ← (ready.mix "DeploymentIncident"
    ["Quarantined", "DeploymentControls"]
    [deploymentIncident.edit .introduce]).mapError .c4
  (incident.mix "DeploymentRecovered"
    ["Recovered", "DeploymentControls"]).mapError .c4

def model : Model := modelResult.toOption.get (by native_decide)

/-- Exact checked policy snapshots; actual requests/entities remain per-call. -/
def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard model schema
    (model.modules.map (·.name)) (by native_decide)

inductive Root where
  | ready
  | incident
  | recovered
  deriving DecidableEq

def Root.name : Root → String
  | .ready => "DeploymentReady"
  | .incident => "DeploymentIncident"
  | .recovered => "DeploymentRecovered"

def publish
     (root : Root)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.Pipeline.DeploymentCase.model CedarPooSpec.Cloud.Pipeline.DeploymentCase.schema :=
      CedarPooSpec.Cloud.Pipeline.DeploymentCase.program) :=
  programContext.publish root.name

structure Choice where
  name : String
  root : String := "DeploymentReady"
  pipeline : GoogleThreatCase.Facts := {}
  attestation : EntityUID := correctAttestation
  releaseReceipt : EntityUID := currentRelease
  releaseReceiptVerified : Bool := true
  currentEpoch : Int64 := 7
  deploymentDigest : String := "sha256:candidate"
  attestationVerified : Bool := true
  immutableReference : Bool := true
  policyEnforced : Bool := true
  expectedPromotion : Bool
  expectedDeployment : Bool

def deployRequest (choice : Choice) : Request :=
  ⟨service, deploy, GoogleThreatCase.candidate, Map.make [
    ("attestation", .prim (.entityUID choice.attestation)),
    ("releaseReceipt", .prim (.entityUID choice.releaseReceipt)),
    ("releaseReceiptVerified", .prim (.bool choice.releaseReceiptVerified)),
    ("currentEpoch", .prim (.int choice.currentEpoch)),
    ("deploymentDigest", .prim (.string choice.deploymentDigest)),
    ("attestationVerified", .prim (.bool choice.attestationVerified)),
    ("immutableReference", .prim (.bool choice.immutableReference)),
    ("policyEnforced", .prim (.bool choice.policyEnforced)),
    ("incidentActive", .prim (.bool choice.pipeline.incidentActive))]⟩

def allowed
     (root : String) (request : Request)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.Pipeline.DeploymentCase.model CedarPooSpec.Cloud.Pipeline.DeploymentCase.schema :=
      CedarPooSpec.Cloud.Pipeline.DeploymentCase.program) : Bool :=
  match programContext.authorize root [request] entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

def promotionAllowed
     (choice : Choice)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.Pipeline.DeploymentCase.model CedarPooSpec.Cloud.Pipeline.DeploymentCase.schema :=
      CedarPooSpec.Cloud.Pipeline.DeploymentCase.program) : Bool :=
  (allowed (programContext := programContext)) choice.root
    (GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline)

def deploymentAllowed
     (choice : Choice)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.Pipeline.DeploymentCase.model CedarPooSpec.Cloud.Pipeline.DeploymentCase.schema :=
      CedarPooSpec.Cloud.Pipeline.DeploymentCase.program) : Bool :=
  (allowed (programContext := programContext)) choice.root (deployRequest choice)

/-- Both decisions must hold for the sample release; the Host still owns
    atomic redemption and actual deployment enforcement. -/
def admitted
     (choice : Choice)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.Pipeline.DeploymentCase.model CedarPooSpec.Cloud.Pipeline.DeploymentCase.schema :=
      CedarPooSpec.Cloud.Pipeline.DeploymentCase.program) : Bool :=
  match programContext.authorize choice.root
      [GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline,
       deployRequest choice] entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

def choices : List Choice := [
  { name := "ready", expectedPromotion := true, expectedDeployment := true },
  { name := "wrong-image-digest", deploymentDigest := "sha256:other",
    expectedPromotion := true, expectedDeployment := false },
  { name := "signed-other-subject", attestation := otherSubject,
    expectedPromotion := true, expectedDeployment := false },
  { name := "other-attestor", attestation := otherAttestor,
    expectedPromotion := true, expectedDeployment := false },
  { name := "unverified-attestation", attestationVerified := false,
    expectedPromotion := true, expectedDeployment := false },
  { name := "unverified-release-receipt", releaseReceiptVerified := false,
    expectedPromotion := true, expectedDeployment := false },
  { name := "receipt-other-digest", releaseReceipt := otherReleaseDigest,
    expectedPromotion := true, expectedDeployment := false },
  { name := "receipt-other-root", releaseReceipt := otherReleaseRoot,
    expectedPromotion := true, expectedDeployment := false },
  { name := "receipt-stale-epoch", releaseReceipt := staleRelease,
    expectedPromotion := true, expectedDeployment := false },
  { name := "mutable-tag", immutableReference := false,
    expectedPromotion := true, expectedDeployment := false },
  { name := "dry-run-policy", policyEnforced := false,
    expectedPromotion := true, expectedDeployment := false },
  { name := "poisoned-runner", pipeline := { cacheIsolated := false },
    releaseReceiptVerified := false,
    expectedPromotion := false, expectedDeployment := false },
  { name := "incident", root := "DeploymentIncident",
    pipeline := { incidentActive := true },
    expectedPromotion := false, expectedDeployment := false },
  { name := "recovered", root := "DeploymentRecovered",
    pipeline := { incidentActive := true },
    expectedPromotion := true, expectedDeployment := true }]

end CedarPooSpec.Cloud.Pipeline.DeploymentCase
