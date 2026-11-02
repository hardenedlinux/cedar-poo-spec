import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Cloud.DataProtection.PseudonymizationGate
import CedarPooSpec.Pseudonymization.Tabular
import CedarPooSpec.Platform.Google.SensitiveDataProtection
import Examples.Cloud.Pipeline.GoogleThreatCase

/-! Synthetic customer profiles combining a release pipeline with a Google
SDP-shaped AES-SIV transformation. The provider REST adapter remains in Rust;
the Host must authenticate its actual response and redeem the effect. -/

namespace CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Pseudonymization CedarPooSpec.Cloud.DataProtection
open CedarPooSpec.Cloud.Pipeline

def datasetType : EntityType := ⟨"Dataset", []⟩
def serviceType : EntityType := ⟨"Service", []⟩
def deidentify : EntityUID := ⟨GoogleThreatCase.actionType, "deidentify"⟩
def service : EntityUID := ⟨serviceType, "data-protection-service"⟩
def dataset : EntityUID := ⟨datasetType, "customer-campaign"⟩
def selectedProfile : EntityUID := ⟨datasetType, "selected-recipe"⟩
def wrongKeyProfile : EntityUID := ⟨datasetType, "other-key-recipe"⟩
def wrongTenantProfile : EntityUID := ⟨datasetType, "other-tenant-recipe"⟩

def lineage : TokenLineage :=
  { tenant := "customer-a", keyDomain := "campaign-key",
    tokenKeyVersion := "dek-a", transformVersion := "canonical-v1",
    wrappingVersion := "kek-a" }

def recipe : AesSivTableRecipe :=
  { dataset := "customer-campaign", valueField := "customer_id",
    contextField := "campaign", admittedContext := some "campaign-a",
    profile := { mode := .aesSiv, scope := "campaign-a", lineage } }

def row : TableRow :=
  { fields := [("customer_id", "synthetic-customer-1"),
      ("campaign", "campaign-a")] }

def selectedInput : AesSivTableInput :=
  (recipe.select row).toOption.get (by native_decide)

def selectedFixture : Lean.Json :=
  CedarPooSpec.Platform.Google.SensitiveDataProtection.selectedTableJson
    recipe selectedInput

def profileData (profile : TokenProfile) : EntityData :=
  { attrs := Map.make [
      ("tenant", .prim (.string profile.lineage.tenant)),
      ("mode", .prim (.string profile.mode.label)),
      ("scope", .prim (.string profile.scope)),
      ("keyDomain", .prim (.string profile.lineage.keyDomain)),
      ("tokenKeyVersion", .prim (.string profile.lineage.tokenKeyVersion)),
      ("transformVersion", .prim (.string profile.lineage.transformVersion)),
      ("admittedContext", .prim (.string "campaign-a")),
      ("artifactDigest", .prim (.string "sha256:candidate"))],
    ancestors := Set.empty, tags := Map.empty }

def datasetEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make
    (["tenant", "mode", "scope", "keyDomain", "tokenKeyVersion",
      "transformVersion", "admittedContext", "artifactDigest"].map
      (fun name => (name, .required .string))), none⟩

def serviceEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.empty, none⟩

def transformContext : RecordType := Map.make [
  ("selectedProfile", .required (.entity datasetType)),
  ("selectedContext", .required .string),
  ("releasedArtifactDigest", .required .string),
  ("keyAuthorized", .required (.bool .anyBool))]

def transformAction : ActionSchemaEntry :=
  ⟨Set.make [serviceType], Set.make [datasetType], Set.empty,
    transformContext⟩

def schema : Schema :=
  ⟨Map.make (GoogleThreatCase.schema.ets.toList ++
      [(datasetType, datasetEntry), (serviceType, serviceEntry)]),
   Map.make (GoogleThreatCase.schema.acts.toList ++
      [(deidentify, transformAction)])⟩

def entities : Entities := Map.make (GoogleThreatCase.entities.toList ++ [
  (service, GoogleThreatCase.emptyData),
  (dataset, profileData recipe.profile),
  (selectedProfile, profileData recipe.profile),
  (wrongKeyProfile, profileData
    { recipe.profile with lineage :=
        { recipe.profile.lineage with tokenKeyVersion := "dek-other" } }),
  (wrongTenantProfile, profileData
    { recipe.profile with lineage :=
        { recipe.profile.lineage with tenant := "customer-b" } }),
  (deidentify, actionSchemaEntryToEntityData transformAction)])

def grant : Policy :=
  { id := "customer-deidentify", effect := .permit,
    principalScope := .principalScope (.eq service),
    actionScope := .actionScope (.eq deidentify),
    resourceScope := .resourceScope (.eq dataset), condition := [] }

def gate : PseudonymizationGate :=
  { policyId := "customer-recipe-gate",
    actionScope := .actionScope (.eq deidentify),
    resourceScope := .resourceScope (.eq dataset) }

/-- The optional data protection profile inherits the same four release
    owners; incident and recovery change only the pipeline's owned veto. -/
def modelResult : Except LeanPoo.Object.CombineError Model := do
  let base ← (Model.define "SdpPermit" [.extend grant]).mapError .c4
  let recipeOwner ← (Model.define "SdpRecipe" [gate.veto.edit .introduce]).mapError .c4
  let protection ← base.combine "SdpPermit" [(recipeOwner, "SdpRecipe")] "SdpReady"
  let combined ← GoogleThreatCase.model.combine "ReleaseReady"
    [(protection, "SdpReady")] "CustomerDataRelease"
  let incident ← (combined.mix "CustomerIncident"
    ["Quarantined", "SdpReady"]).mapError .c4
  (incident.mix "CustomerRecovered" ["Recovered", "SdpReady"]).mapError .c4

def model : Model := modelResult.toOption.get (by native_decide)

/-- Exact checked policy snapshots; actual requests/entities remain per-call. -/
def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard model schema
    (model.modules.map (·.name)) (by native_decide)

structure Choice where
  name : String
  root : String
  pipeline : GoogleThreatCase.Facts := {}
  profile : EntityUID := selectedProfile
  context : String := selectedInput.context
  digest : String := "sha256:candidate"
  keyAuthorized : Bool := true
  expectedPipeline : Bool
  expectedTransform : Bool

def transformRequest (choice : Choice) : Request :=
  ⟨service, deidentify, dataset, Map.make [
    ("selectedProfile", .prim (.entityUID choice.profile)),
    ("selectedContext", .prim (.string choice.context)),
    ("releasedArtifactDigest", .prim (.string choice.digest)),
    ("keyAuthorized", .prim (.bool choice.keyAuthorized))]⟩

def allowed
     (root : String) (request : Request)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.model CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.schema :=
      CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.program) : Bool :=
  match programContext.authorize root [request] entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

def pipelineAllowed
     (choice : Choice)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.model CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.schema :=
      CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.program) : Bool :=
  (allowed (programContext := programContext)) choice.root (GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline)

def transformAllowed
     (choice : Choice)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.model CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.schema :=
      CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.program) : Bool :=
  (allowed (programContext := programContext)) choice.root (transformRequest choice)

/-- The sample Host admission checks both decisions before dispatching the
    provider effect; production redemption still needs an atomic receipt. -/
def admitted
     (choice : Choice)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.model CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.schema :=
      CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease.program) : Bool :=
  match programContext.authorize choice.root
      [GoogleThreatCase.request GoogleThreatCase.candidate choice.pipeline,
       transformRequest choice] entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

def choices : List Choice := [
  { name := "pipeline-only", root := "ReleaseReady",
    expectedPipeline := true, expectedTransform := false },
  { name := "combined-ready", root := "CustomerDataRelease",
    expectedPipeline := true, expectedTransform := true },
  { name := "other-recipe-key", root := "CustomerDataRelease",
    profile := wrongKeyProfile,
    expectedPipeline := true, expectedTransform := false },
  { name := "other-tenant-profile", root := "CustomerDataRelease",
    profile := wrongTenantProfile,
    expectedPipeline := true, expectedTransform := false },
  { name := "other-row-context", root := "CustomerDataRelease",
    context := "campaign-b",
    expectedPipeline := true, expectedTransform := false },
  { name := "other-released-digest", root := "CustomerDataRelease",
    digest := "sha256:other",
    expectedPipeline := true, expectedTransform := false },
  { name := "key-not-authorized", root := "CustomerDataRelease",
    keyAuthorized := false,
    expectedPipeline := true, expectedTransform := false },
  { name := "poisoned-runner", root := "CustomerDataRelease",
    pipeline := { cacheIsolated := false },
    expectedPipeline := false, expectedTransform := true },
  { name := "incident-suspends-release", root := "CustomerIncident",
    pipeline := { incidentActive := true },
    expectedPipeline := false, expectedTransform := true },
  { name := "recovery-restores-release", root := "CustomerRecovered",
    pipeline := { incidentActive := true },
    expectedPipeline := true, expectedTransform := true }]

end CedarPooSpec.Cloud.DataProtection.GoogleSdpRelease
