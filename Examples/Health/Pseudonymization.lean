import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Revision
import CedarPooSpec.PolicyValidation
import CedarPooSpec.Governance.Veto
import CedarPooSpec.Admission.BoundOperation
import CedarPooSpec.Data.Relation
import CedarPooSpec.Pseudonymization

/-!
An authorization model for hospital pseudonymization. The cryptographic
operations, IV allocation, key release, and durable audit are Host effects;
the finite Cedar model authorizes requests using facts established by them.
-/

namespace CedarPooSpec.PseudonymizationExample

open Cedar.Spec Cedar.Validation Cedar.Data
open CedarPooSpec.PolicyModules
open CedarPooSpec.Governance
open CedarPooSpec.Admission
open CedarPooSpec.Data
open CedarPooSpec.Pseudonymization
open LeanPoo.Proof

def actorType : EntityType := ⟨"Actor", []⟩
def datasetType : EntityType := ⟨"Dataset", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def tokenize : EntityUID := ⟨actionType, "tokenize"⟩
def join : EntityUID := ⟨actionType, "join"⟩
def reidentify : EntityUID := ⟨actionType, "reidentify"⟩
def releaseResult : EntityUID := ⟨actionType, "release-result"⟩

def actorEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("tenant", .required .string), ("kind", .required .string)], none⟩
def datasetEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.make [
    ("tenant", .required .string), ("mode", .required .string),
    ("scope", .required .string), ("keyDomain", .required .string),
    ("tokenKeyVersion", .required .string),
    ("transformVersion", .required .string),
    ("wrappingVersion", .required .string)], none⟩
def contextType : RecordType := Map.make [
  ("targetDataset", .required (.entity datasetType)),
  ("ownerApproved", .required (.bool .anyBool)),
  ("keyAuthorized", .required (.bool .anyBool)),
  ("requestedKeyVersion", .required .string),
  ("joinApproved", .required (.bool .anyBool)),
  ("releaseApproved", .required (.bool .anyBool)),
  ("budgetAvailable", .required (.bool .anyBool)),
  ("reidentifyApproved", .required (.bool .anyBool)),
  ("auditReady", .required (.bool .anyBool)),
  ("ivUnique", .required (.bool .anyBool))]
def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [actorType], Set.make [datasetType], Set.empty, contextType⟩
def schema : Schema :=
  ⟨Map.make [(actorType, actorEntry), (datasetType, datasetEntry)],
   Map.make [(tokenize, actionEntry), (join, actionEntry),
     (reidentify, actionEntry), (releaseResult, actionEntry)]⟩

def agent : EntityUID := ⟨actorType, "analytics-agent"⟩
def steward : EntityUID := ⟨actorType, "clinical-steward"⟩
def operator : EntityUID := ⟨actorType, "data-operator"⟩
def ingest : EntityUID := ⟨actorType, "trusted-ingestion"⟩
def hospital : EntityUID := ⟨datasetType, "hospital-patients"⟩
def research : EntityUID := ⟨datasetType, "research-patients"⟩
def randomized : EntityUID := ⟨datasetType, "randomized-records"⟩
def oneWay : EntityUID := ⟨datasetType, "one-way-records"⟩
def otherKey : EntityUID := ⟨datasetType, "other-key-records"⟩
def otherTenant : EntityUID := ⟨datasetType, "other-tenant-records"⟩
def rewrapped : EntityUID := ⟨datasetType, "rewrapped-records"⟩
def rotatedTokenKey : EntityUID := ⟨datasetType, "rotated-token-key-records"⟩
def revisedTransform : EntityUID := ⟨datasetType, "revised-transform-records"⟩
def actorData (kind : String) : EntityData :=
  { attrs := Map.make [("tenant", .prim (.string "hospital-a")),
      ("kind", .prim (.string kind))], ancestors := Set.empty, tags := Map.empty }

def hospitalLineage : TokenLineage :=
  { tenant := "hospital-a", keyDomain := "key-a",
    tokenKeyVersion := "dek-v1", transformVersion := "patient-id-v1",
    wrappingVersion := "kek-v1" }

def datasetData (mode : Mode) (scope : String) (lineage : TokenLineage := hospitalLineage) : EntityData :=
  { attrs := Map.make [("tenant", .prim (.string lineage.tenant)),
      ("mode", .prim (.string mode.label)), ("scope", .prim (.string scope)),
      ("keyDomain", .prim (.string lineage.keyDomain)),
      ("tokenKeyVersion", .prim (.string lineage.tokenKeyVersion)),
      ("transformVersion", .prim (.string lineage.transformVersion)),
      ("wrappingVersion", .prim (.string lineage.wrappingVersion))],
    ancestors := Set.empty, tags := Map.empty }

/-- One declared dataset is the source of both Cedar entity data and catalog
    admission checks. The Host must verify that these declarations match the
    actual transformation and key inventory before publication. -/
structure DatasetObject where
  uid : EntityUID
  mode : Mode
  scope : String
  lineage : TokenLineage := hospitalLineage

def DatasetObject.profile (object : DatasetObject) : TokenProfile :=
  { mode := object.mode, scope := object.scope, lineage := object.lineage }

def DatasetObject.entity (object : DatasetObject) : EntityUID × EntityData :=
  (object.uid, datasetData object.mode object.scope object.lineage)

def datasets : List DatasetObject := [
  ⟨hospital, .aesSiv, "hospital-a", hospitalLineage⟩,
  ⟨research, .aesSiv, "study-1", hospitalLineage⟩,
  ⟨randomized, .aesGcm, "hospital-a", hospitalLineage⟩,
  ⟨oneWay, .hmacSha256, "hospital-a", hospitalLineage⟩,
  ⟨otherKey, .aesSiv, "hospital-a", { hospitalLineage with keyDomain := "key-b" }⟩,
  ⟨otherTenant, .aesSiv, "hospital-a", { hospitalLineage with tenant := "hospital-b" }⟩,
  ⟨rewrapped, .aesSiv, "hospital-a", { hospitalLineage with wrappingVersion := "kek-v2" }⟩,
  ⟨rotatedTokenKey, .aesSiv, "hospital-a", { hospitalLineage with tokenKeyVersion := "dek-v2" }⟩,
  ⟨revisedTransform, .aesSiv, "hospital-a",
    { hospitalLineage with transformVersion := "patient-id-v2" }⟩]

/-- The Google HMAC transformation has no context tweak. Separate scopes
    therefore need separate HMAC key material to prevent passive linkage. -/
def hmacCatalogSeparated (catalog : List DatasetObject) : Bool :=
  CedarPooSpec.Pseudonymization.hmacCatalogSeparated
    (catalog.map DatasetObject.profile)

def unsafeHmacStudy : DatasetObject :=
  ⟨⟨datasetType, "unsafe-hmac-study"⟩, .hmacSha256, "study-1", hospitalLineage⟩
def isolatedHmacStudy : DatasetObject :=
  ⟨⟨datasetType, "isolated-hmac-study"⟩, .hmacSha256, "study-1",
    { hospitalLineage with keyDomain := "study-1-hmac-key" }⟩

theorem publishedHmacCatalogSeparated : hmacCatalogSeparated datasets = true := by
  native_decide
theorem unsafeHmacStudyRejected :
    hmacCatalogSeparated (unsafeHmacStudy :: datasets) = false := by
  native_decide
theorem isolatedHmacStudyAccepted :
    hmacCatalogSeparated (isolatedHmacStudy :: datasets) = true := by
  native_decide

def entities : Entities := Map.make ([
  (agent, actorData "agent"), (steward, actorData "steward"),
  (operator, actorData "operator"),
  (ingest, actorData "ingest")] ++
  datasets.map DatasetObject.entity ++ [
  (tokenize, actionSchemaEntryToEntityData actionEntry),
  (join, actionSchemaEntryToEntityData actionEntry),
  (reidentify, actionSchemaEntryToEntityData actionEntry),
  (releaseResult, actionSchemaEntryToEntityData actionEntry)])

def attr (source : Var) (name : String) : Expr := .getAttr (.var source) name
def fact (name : String) : Expr := attr .context name
def resource (name : String) : Expr := attr .resource name
def eqString (left : Expr) (right : String) : Expr :=
  .binaryApp .eq left (.lit (.string right))
def equal (left right : Expr) : Expr := .binaryApp .eq left right
def not (body : Expr) : Expr := .unaryApp .not body
def target (name : String) : Expr := .getAttr (fact "targetDataset") name
def tokenRelation : TokenRelation :=
  { source := fact "targetDataset", target := .var .resource }
def tenantBound : Expr := equal (attr .principal "tenant") (resource "tenant")
def targetTenantBound : Expr := equal (attr .principal "tenant") (target "tenant")
def selfBound : Expr := equal (fact "targetDataset") (.var .resource)
def modeIs (mode : String) : Expr := eqString (resource "mode") mode
def compatible (mode : String) : Expr :=
  .and (modeIs mode) tokenRelation.sameRecipe
def keyed (mode : String) : Expr :=
  .and (compatible mode) (.and (fact "keyAuthorized")
    (equal (fact "requestedKeyVersion") (resource "tokenKeyVersion")))

def policy (id : String) (effect : Effect) (action : EntityUID)
    (body : Expr) : Policy :=
  { id := id, effect := effect,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := body }] }

structure CryptoProfile where
  name : String
  mode : Mode

def CryptoProfile.module (profile : CryptoProfile) : Module := Id.run do
  let mode := profile.mode.label
  let basis := compatible mode
  let withKey := keyed mode
  let tokenizeBody :=
    if profile.mode == .aesGcm then
      .and withKey (.and selfBound
        (.and (eqString (attr .principal "kind") "ingest") (fact "ivUnique")))
    else .and withKey (.and selfBound
      (eqString (attr .principal "kind") "ingest"))
  let mut edits : List Edit :=
    [.extend (policy "tokenize" .permit tokenize tokenizeBody)]
  if profile.mode.linkable then
    edits := edits ++ [.extend (policy "join" .permit join
      (.and basis (.and targetTenantBound (fact "joinApproved"))))]
  else
    edits := edits ++ [.extend (policy "no-deterministic-join" .forbid join
      (modeIs mode))]
  if profile.mode.reversible then
    edits := edits ++ [.extend (policy "reidentify" .permit reidentify
      (.and withKey (.and selfBound
        (.and (eqString (attr .principal "kind") "steward")
          (.and (fact "reidentifyApproved") (fact "auditReady"))))))]
  else
    edits := edits ++ [.extend (policy "irreversible-token" .forbid
      reidentify (modeIs mode))]
  return { name := profile.name, parentOrders := [["Base"]], edits }

def siv : CryptoProfile := ⟨"AesSiv", .aesSiv⟩
def gcm : CryptoProfile := ⟨"AesGcm", .aesGcm⟩
def hmac : CryptoProfile := ⟨"Hmac", .hmacSha256⟩

def legacyReveal : Policy :=
  policy "legacy-reidentify" .permit reidentify (.lit (.bool true))
def base : Module := { name := "Base", edits := [.extend legacyReveal] }
def veto (id : String) (action : EntityUID) (denyWhen : Expr) : Veto :=
  { policyId := id, actionScope := .actionScope (.eq action), denyWhen }

def owner : Module :=
  Veto.moduleMany "DataOwner" "Base" .introduce [
    veto "owner-approval" tokenize (not (fact "ownerApproved")),
    veto "owner-join-approval" join (not (fact "ownerApproved")),
    veto "owner-reidentify-approval" reidentify (not (fact "ownerApproved"))]
def privacy : Module :=
  Veto.moduleMany "Privacy" "Base" .introduce [
    veto "tenant-token-boundary" tokenize (not tenantBound),
    veto "tenant-join-boundary" join (not tenantBound),
    veto "tenant-reidentify-boundary" reidentify (not tenantBound)]
def agentBoundary : Module :=
  (veto "agent-cannot-reidentify" reidentify
    (eqString (attr .principal "kind") "agent")).module
      "AgentBoundary" "Base" .introduce

/-- Each view inherits the same owner, privacy, and agent boundaries. Changing
    the profile changes only the cryptographic capability branch. -/
structure GovernanceView where
  name : String
  profile : CryptoProfile

def GovernanceView.module (view : GovernanceView) : Module :=
  { name := view.name,
    parentOrders := [[view.profile.name, "DataOwner", "Privacy", "AgentBoundary"]],
    edits := [.remove legacyReveal.id] }
def hospitalView : GovernanceView := ⟨"HospitalSiv", siv⟩
def randomizedView : GovernanceView := ⟨"RandomizedGcm", gcm⟩
def oneWayView : GovernanceView := ⟨"OneWayHmac", hmac⟩
def views : List GovernanceView := [hospitalView, randomizedView, oneWayView]

/-- Releasing an analytical result is a distinct owned permission from
    joining stored tokens. The Host authenticates approval and consumes its
    budget in the same transaction that releases the result. -/
def resultReleaseControl : ResultRelease :=
  { permitId := "release-result", ownerVetoId := "release-owner-approval",
    actionScope := .actionScope (.eq releaseResult),
    sameTarget := selfBound, tenantBound,
    actorAllowed := eqString (attr .principal "kind") "agent",
    targetTenantBound,
    ownerApproved := fact "ownerApproved",
    releaseApproved := fact "releaseApproved",
    budgetAvailable := fact "budgetAvailable" }
def resultRelease : Module :=
  { name := "ResultRelease", parentOrders := [[hospitalView.name]],
    edits := resultReleaseControl.edits .introduce }

def incidentControl : Veto :=
  veto "agent-join-suspended" join (eqString (attr .principal "kind") "agent")
def incident : Module :=
  incidentControl.module "AgentIncident" hospitalView.name .introduce
def recovered : Module :=
  incidentControl.module "Recovered" incident.name .withdraw
def modelResult : Except LeanPoo.C4.Error Model := do
  let initial : Model := { modules := [base] }
  let profiles ← [siv, gcm, hmac].foldlM (fun current profile =>
    current.extend profile.name "Base" profile.module.edits) initial
  let dataOwner ← profiles.extend owner.name "Base" owner.edits
  let privateView ← dataOwner.extend privacy.name "Base" privacy.edits
  let agentView ← privateView.extend agentBoundary.name "Base" agentBoundary.edits
  let governed ← views.foldlM (fun current view =>
    current.mix view.name
      [view.profile.name, "DataOwner", "Privacy", "AgentBoundary"]
      view.module.edits) agentView
  let suspended ← governed.extend incident.name hospitalView.name incident.edits
  let restored ← suspended.extend recovered.name incident.name recovered.edits
  restored.extend resultRelease.name hospitalView.name resultRelease.edits

def model : Model := modelResult.toOption.get (by native_decide)

/-- Exact checked policy snapshots; actual requests/entities remain per-call. -/
def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard model schema
    (model.modules.map (·.name)) (by native_decide)

structure Facts where
  targetDataset : EntityUID := hospital
  ownerApproved : Bool := true
  keyAuthorized : Bool := true
  requestedKeyVersion : String := "dek-v1"
  joinApproved : Bool := true
  releaseApproved : Bool := false
  budgetAvailable : Bool := false
  reidentifyApproved : Bool := false
  auditReady : Bool := false
  ivUnique : Bool := true

def request (who action dataset : EntityUID) (facts : Facts) : Request :=
  ⟨who, action, dataset, Map.make [
    ("targetDataset", .prim (.entityUID facts.targetDataset)),
    ("ownerApproved", .prim (.bool facts.ownerApproved)),
    ("keyAuthorized", .prim (.bool facts.keyAuthorized)),
    ("requestedKeyVersion", .prim (.string facts.requestedKeyVersion)),
    ("joinApproved", .prim (.bool facts.joinApproved)),
    ("releaseApproved", .prim (.bool facts.releaseApproved)),
    ("budgetAvailable", .prim (.bool facts.budgetAvailable)),
    ("reidentifyApproved", .prim (.bool facts.reidentifyApproved)),
    ("auditReady", .prim (.bool facts.auditReady)),
    ("ivUnique", .prim (.bool facts.ivUnique))]⟩

/-- The operation names the dataset and key revision used for a concrete
    tokenization request. The Host must verify these values against its key
    inventory and actual execution payload. -/
def tokenizeRequest (datasetId keyVersion : String) : Request :=
  let dataset : EntityUID := ⟨datasetType, datasetId⟩
  request ingest tokenize dataset
    { targetDataset := dataset, requestedKeyVersion := keyVersion }

def tokenization : BoundOperation String String tokenizeRequest :=
  ⟨"hospital-patients", "dek-v1"⟩

theorem tokenizationBindsEffectAndRevision :
    tokenization.matches "hospital-patients" "dek-v1" = true ∧
    tokenization.matches "research-patients" "dek-v1" = false ∧
    tokenization.matches "hospital-patients" "dek-v2" = false := by
  native_decide

theorem tokenizationAuthorizationUsesBoundRequest :
    (match tokenization.authorize "hospital-patients" "dek-v1"
        model "HospitalSiv" entities with
    | .ok receipt => receipt.allowed
    | .error _ => false) = true := by
  native_decide

theorem substitutedEffectRejectedBeforeCedar :
    (match tokenization.authorize "research-patients" "dek-v1"
        model "HospitalSiv" entities with
    | .error .effectMismatch => true
    | _ => false) = true := by
  native_decide

theorem staleStateRejectedBeforeCedar :
    (match tokenization.authorize "hospital-patients" "dek-v2"
        model "HospitalSiv" entities with
    | .error .stateMismatch => true
    | _ => false) = true := by
  native_decide

theorem changedKeyRevisionCannotReuseTokenizationDecision :
    (match (⟨"hospital-patients", "dek-v2"⟩ :
        BoundOperation String String tokenizeRequest).authorize
          "hospital-patients" "dek-v2" model "HospitalSiv" entities with
    | .ok receipt => receipt.allowed
    | .error _ => false) = false := by
  native_decide

def reveal : Facts := { reidentifyApproved := true, auditReady := true }
def cases : List (String × String × Request × Decision) := [
  ("pre-governance-broad-reidentify", "AesSiv",
    request steward reidentify hospital {}, .allow),
  ("hospital-tokenize", "HospitalSiv", request ingest tokenize hospital {}, .allow),
  ("tokenize-without-key", "HospitalSiv", request ingest tokenize hospital
    { keyAuthorized := false }, .deny),
  ("agent-tokenization-oracle", "HospitalSiv",
    request agent tokenize hospital {}, .deny),
  ("hospital-join", "HospitalSiv", request agent join hospital {}, .allow),
  ("join-without-key-release", "HospitalSiv", request agent join hospital
    { keyAuthorized := false }, .allow),
  ("research-local-join", "HospitalSiv", request agent join research
    { targetDataset := research }, .allow),
  ("approved-result-release", "ResultRelease", request agent releaseResult hospital
    { releaseApproved := true, budgetAvailable := true }, .allow),
  ("result-release-without-approval", "ResultRelease", request agent releaseResult hospital
    { budgetAvailable := true }, .deny),
  ("result-release-budget-exhausted", "ResultRelease", request agent releaseResult hospital
    { releaseApproved := true }, .deny),
  ("result-release-owner-revoked", "ResultRelease", request agent releaseResult hospital
    { releaseApproved := true, budgetAvailable := true, ownerApproved := false }, .deny),
  ("result-release-other-dataset", "ResultRelease", request agent releaseResult hospital
    { releaseApproved := true, budgetAvailable := true, targetDataset := research }, .deny),
  ("result-release-wrong-actor", "ResultRelease", request operator releaseResult hospital
    { releaseApproved := true, budgetAvailable := true }, .deny),
  ("cross-study-join", "HospitalSiv", request agent join research {}, .deny),
  ("wrong-key-domain", "HospitalSiv", request agent join hospital
    { targetDataset := otherKey }, .deny),
  ("rewrapped-same-token-key", "HospitalSiv", request agent join hospital
    { targetDataset := rewrapped }, .allow),
  ("rotated-token-key", "HospitalSiv", request agent join hospital
    { targetDataset := rotatedTokenKey }, .deny),
  ("revised-transform", "HospitalSiv", request agent join hospital
    { targetDataset := revisedTransform }, .deny),
  ("incompatible-token-mode", "HospitalSiv", request agent join hospital
    { targetDataset := randomized }, .deny),
  ("other-tenant-join", "HospitalSiv", request agent join hospital
    { targetDataset := otherTenant }, .deny),
  ("tokenize-other-dataset", "HospitalSiv", request ingest tokenize hospital
    { targetDataset := otherKey }, .deny),
  ("owner-rejected", "HospitalSiv", request agent join hospital
    { ownerApproved := false }, .deny),
  ("agent-reidentify", "HospitalSiv", request agent reidentify hospital reveal, .deny),
  ("operator-reidentify", "HospitalSiv", request operator reidentify hospital reveal, .deny),
  ("reidentify-other-dataset", "HospitalSiv", request steward reidentify hospital
    { reveal with targetDataset := otherKey }, .deny),
  ("steward-reidentify", "HospitalSiv", request steward reidentify hospital reveal, .allow),
  ("reidentify-without-key", "HospitalSiv", request steward reidentify hospital
    { reveal with keyAuthorized := false }, .deny),
  ("wrong-reidentification-key-version", "HospitalSiv",
    request steward reidentify hospital
      { reveal with requestedKeyVersion := "dek-v2" }, .deny),
  ("rotated-key-reidentify", "HospitalSiv",
    request steward reidentify rotatedTokenKey
      { reveal with targetDataset := rotatedTokenKey, requestedKeyVersion := "dek-v2" }, .allow),
  ("no-reidentify-approval", "HospitalSiv", request steward reidentify hospital
    { reveal with reidentifyApproved := false }, .deny),
  ("audit-unavailable", "HospitalSiv", request steward reidentify hospital
    { reveal with auditReady := false }, .deny),
  ("gcm-unique-iv", "RandomizedGcm", request ingest tokenize randomized
    { targetDataset := randomized }, .allow),
  ("gcm-reused-iv", "RandomizedGcm", request ingest tokenize randomized
    { targetDataset := randomized, ivUnique := false }, .deny),
  ("gcm-no-deterministic-join", "RandomizedGcm", request agent join randomized
    { targetDataset := randomized }, .deny),
  ("gcm-steward-reidentify", "RandomizedGcm", request steward reidentify randomized
    { reveal with targetDataset := randomized }, .allow),
  ("hmac-local-join", "OneWayHmac", request agent join oneWay
    { targetDataset := oneWay }, .allow),
  ("hmac-tokenize", "OneWayHmac", request ingest tokenize oneWay
    { targetDataset := oneWay }, .allow),
  ("hmac-no-reidentification", "OneWayHmac", request steward reidentify oneWay
    { reveal with targetDataset := oneWay }, .deny),
  ("incident-agent-join", "AgentIncident", request agent join hospital {}, .deny),
  ("incident-steward-join", "AgentIncident", request steward join hospital {}, .allow),
  ("recovered-agent-join", "Recovered", request agent join hospital {}, .allow)]

def scenarioConforms
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PseudonymizationExample.model CedarPooSpec.PseudonymizationExample.schema :=
      CedarPooSpec.PseudonymizationExample.program) : Bool := cases.all fun (_, root, req, expected) =>
  match programContext.authorize root [req] entities with
  | .error _ => false
  | .ok receipt => receipt.responses.all fun response =>
      response.decision == expected && response.erroringPolicies.isEmpty

def composedViewsShareRemoval : Bool :=
  views.all (fun view => view.module.edits == [.remove legacyReveal.id])

def compositionIsLocal : Bool :=
  let sivAffected := invalidatedNodes model.graph [siv.name]
  let incidentAffected := invalidatedNodes model.graph [incident.name]
  sivAffected.contains hospitalView.name &&
  sivAffected.contains incident.name &&
  !sivAffected.contains randomizedView.name &&
  !sivAffected.contains oneWayView.name &&
  incidentAffected.contains incident.name &&
  incidentAffected.contains recovered.name &&
  !incidentAffected.contains randomizedView.name

def incidentOnlyAddsAgentVeto : Bool :=
  match model.compile hospitalView.name, model.compile incident.name with
  | .ok baseline, .ok suspended =>
    suspended.length == baseline.length + 1 &&
    suspended.filter (fun p => p.id != "agent-join-suspended") == baseline
  | _, _ => false

end CedarPooSpec.PseudonymizationExample
