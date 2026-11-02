import Examples.Health.PriorAuthorization.PriorAuthorization
import CedarPooSpec.Vertical.Health.DisclosureProfile
import CedarPooSpec.Functional.Capabilities

/-!
The same provider workflow has two internal boundaries that the payer-submit
policy cannot cover: delegation to a verification agent and shared memory.
The envelope is a synthetic host projection, not an inspection of LLM text.
-/

namespace CedarPooSpec.PriorAuthorizationInternalChannels

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Vertical.Health
open CedarPooSpec.PriorAuthorizationExample

def verifierType : EntityType := ⟨"VerificationAgent", []⟩
def memoryType : EntityType := ⟨"AgentMemory", []⟩
def verifier : EntityUID := ⟨verifierType, "provider-verifier"⟩
def memory : EntityUID := ⟨memoryType, "provider-memory"⟩
def delegate : EntityUID := ⟨actionType, "delegate-verification"⟩
def remember : EntityUID := ⟨actionType, "write-shared-memory"⟩

def channelContextType : RecordType := Map.make [
  ("purpose", .required .string),
  ("payloadClass", .required .string),
  ("patientMatches", .required (.bool .anyBool)),
  ("delegationActive", .required (.bool .anyBool))]
def delegateEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [verifierType], Set.empty, channelContextType⟩
def rememberEntry : ActionSchemaEntry :=
  ⟨Set.make [agentType], Set.make [memoryType], Set.empty, channelContextType⟩
def schema : Schema :=
  ⟨Map.make (PriorAuthorizationExample.schema.ets.toList ++
      [(verifierType, emptyEntry), (memoryType, emptyEntry)]),
    Map.make (PriorAuthorizationExample.schema.acts.toList ++
      [(delegate, delegateEntry), (remember, rememberEntry)])⟩
def entities : Entities := Map.make (PriorAuthorizationExample.entities.toList ++ [
  (verifier, emptyData), (memory, emptyData),
  (delegate, actionSchemaEntryToEntityData delegateEntry),
  (remember, actionSchemaEntryToEntityData rememberEntry)])

def verificationTemplate : DisclosureChannel :=
  { policyId := "delegate-verification", action := delegate,
    destination := verifier, purpose := "verify-prior-authorization",
    payloadClass := "verification-token" }
def verificationProfile : DisclosureProfile.Object :=
  (DisclosureProfile.define "VerificationChannel" verificationTemplate).toOption.get
    (by native_decide)

/-- One admission for all projections of this exact immutable profile. -/
def verificationProfileAccess : CedarPooSpec.Functional.ObjectProfile.Session DisclosureProfile.contract (CedarPooSpec.Functional.ObjectProfile.factory DisclosureProfile.contract) verificationProfile :=
  (CedarPooSpec.Functional.ObjectProfile.Session.open DisclosureProfile.contract
    (CedarPooSpec.Functional.ObjectProfile.factory DisclosureProfile.contract) verificationProfile).toOption.get (by native_decide)

def verificationObject : DisclosureChannel :=
  (verificationProfileAccess.read .channel).get (by native_decide)

def memoryProfile : DisclosureProfile.Object :=
  (verificationProfile.extendWith "MemoryChannel" do
    LeanPoo.Object.Dataflow.Builder.value .policyId "write-shared-memory"
    LeanPoo.Object.Dataflow.Builder.value .action remember
    LeanPoo.Object.Dataflow.Builder.value .destination memory
    LeanPoo.Object.Dataflow.Builder.value .purpose "resume-prior-authorization"
    LeanPoo.Object.Dataflow.Builder.value .payloadClass "workflow-handle").toOption.get
      (by native_decide)

/-- One admission for all projections of this exact immutable profile. -/
def memoryProfileAccess : CedarPooSpec.Functional.ObjectProfile.Session DisclosureProfile.contract (CedarPooSpec.Functional.ObjectProfile.factory DisclosureProfile.contract) memoryProfile :=
  (CedarPooSpec.Functional.ObjectProfile.Session.open DisclosureProfile.contract
    (CedarPooSpec.Functional.ObjectProfile.factory DisclosureProfile.contract) memoryProfile).toOption.get (by native_decide)

def memoryObject : DisclosureChannel :=
  (memoryProfileAccess.read .channel).get (by native_decide)

def verificationPolicy : Policy :=
  (verificationProfileAccess.read .policy).get (by native_decide)

def memoryPolicy : Policy :=
  (memoryProfileAccess.read .policy).get (by native_decide)
def revokedChannel : Policy :=
  policy "revoked-internal-delegation" .forbid
    (.actionInAny [delegate, remember]) .any (not_ (fact "delegationActive"))
def memoryFreeze : Policy :=
  policy "shared-memory-incident" .forbid (.actionScope (.eq remember))
    (.eq memory) (.lit (.bool true))

/-- The existing external boundary is inherited; independently owned
    minimization and delegation changes meet at a C4 mix. -/
def modelResult : Except LeanPoo.C4.Error Model := do
  let handoff ← PriorAuthorizationExample.model.extend
    "VerificationHandoff" "Governed" [verificationObject.introduce]
  let stored ← handoff.extend "SharedMemory" "Governed"
    [memoryObject.introduce]
  let base ← stored.mix "ChannelBase" ["VerificationHandoff", "SharedMemory"]
  let privacy ← base.extend "ChannelPrivacy" "ChannelBase"
    [.overlay verificationPolicy, .overlay memoryPolicy]
  let temporal ← privacy.extend "ChannelTemporal" "ChannelBase"
    [.extend revokedChannel]
  let combined ← temporal.mix "ChannelGoverned"
    ["ChannelPrivacy", "ChannelTemporal"]
  let removed ← combined.extend "MemoryRemoved" "ChannelGoverned"
    [memoryObject.withdraw]
  let incident ← removed.extend "ChannelIncident" "ChannelGoverned"
    [.extend memoryFreeze]
  incident.extend "ChannelRecovered" "ChannelIncident" [.remove memoryFreeze.id]

def model : Model := modelResult.toOption.get (by native_decide)

def roots : List String :=
  ["VerificationHandoff", "SharedMemory", "ChannelBase", "ChannelPrivacy", "ChannelTemporal",
    "ChannelGoverned", "MemoryRemoved", "ChannelIncident", "ChannelRecovered"]

def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard model schema roots
      (by native_decide)

inductive Payload where
  | verificationToken | workflowHandle | fullChart
  deriving BEq, DecidableEq

def Payload.className : Payload → String
  | .verificationToken => "verification-token"
  | .workflowHandle => "workflow-handle"
  | .fullChart => "full-chart"

structure Envelope where
  action : EntityUID
  resource : EntityUID
  purpose : String
  payload : Payload
  patientMatches : Bool := true
  delegationActive : Bool := true

def request (envelope : Envelope) : Request :=
  ⟨agent, envelope.action, envelope.resource, Map.make [
    ("purpose", .prim (.string envelope.purpose)),
    ("payloadClass", .prim (.string envelope.payload.className)),
    ("patientMatches", .prim (.bool envelope.patientMatches)),
    ("delegationActive", .prim (.bool envelope.delegationActive))]⟩

def admitted
     (root : String) (envelope : Envelope)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PriorAuthorizationInternalChannels.model CedarPooSpec.PriorAuthorizationInternalChannels.schema :=
      CedarPooSpec.PriorAuthorizationInternalChannels.program) : Bool :=
  match programContext.authorize root [request envelope] entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

/-- Replace this synthetic boundary with a host connector that projects the
    real immutable payload and performs the authorized effect. -/
structure Port (m : Type → Type) (Raw : Type) where
  project : Raw → m Envelope
  deliver : Raw → m Unit

def Port.submit
     [Monad m] (port : Port m Raw) (root : String) (raw : Raw)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PriorAuthorizationInternalChannels.model CedarPooSpec.PriorAuthorizationInternalChannels.schema :=
      CedarPooSpec.PriorAuthorizationInternalChannels.program) : m Bool := do
  let envelope ← port.project raw
  if (admitted (programContext := programContext)) root envelope then
    port.deliver raw
    return true
  return false

def syntheticPort : Port (StateM (List Payload)) Envelope where
  project := pure
  deliver := fun envelope => modify (fun delivered => delivered ++ [envelope.payload])

def syntheticDelivery (root : String) (envelope : Envelope) : Bool × List Payload :=
  (syntheticPort.submit root envelope).run []

def token : Envelope :=
  ⟨delegate, verifier, "verify-prior-authorization", .verificationToken, true, true⟩
def chart : Envelope := { token with payload := .fullChart }
def wrongPatient : Envelope := { token with patientMatches := false }
def revoked : Envelope := { token with delegationActive := false }
def handle : Envelope :=
  ⟨remember, memory, "resume-prior-authorization", .workflowHandle, true, true⟩
def chartInMemory : Envelope := { handle with payload := .fullChart }
def wrongPurpose : Envelope := { handle with purpose := "general-agent-memory" }

def cases : List (String × String × Envelope × Bool) := [
  ("handoff-object-appends-delegation", "VerificationHandoff", chart, true),
  ("handoff-object-has-no-memory", "VerificationHandoff", chartInMemory, false),
  ("memory-object-appends-storage", "SharedMemory", chartInMemory, true),
  ("memory-object-has-no-delegation", "SharedMemory", chart, false),
  ("broad-delegate-chart", "ChannelBase", chart, true),
  ("broad-memory-chart", "ChannelBase", chartInMemory, true),
  ("privacy-owner-misses-revocation", "ChannelPrivacy", revoked, true),
  ("temporal-owner-misses-chart", "ChannelTemporal", chart, true),
  ("minimal-delegate-token", "ChannelGoverned", token, true),
  ("minimal-delegate-chart", "ChannelGoverned", chart, false),
  ("minimal-delegate-wrong-patient", "ChannelGoverned", wrongPatient, false),
  ("minimal-delegate-revoked", "ChannelGoverned", revoked, false),
  ("minimal-memory-handle", "ChannelGoverned", handle, true),
  ("minimal-memory-revoked", "ChannelGoverned",
    { handle with delegationActive := false }, false),
  ("minimal-memory-chart", "ChannelGoverned", chartInMemory, false),
  ("minimal-memory-wrong-purpose", "ChannelGoverned", wrongPurpose, false),
  ("memory-object-removed", "MemoryRemoved", handle, false),
  ("memory-removal-keeps-delegation", "MemoryRemoved", token, true),
  ("incident-freezes-memory", "ChannelIncident", handle, false),
  ("incident-keeps-delegation", "ChannelIncident", token, true),
  ("recovery-restores-memory", "ChannelRecovered", handle, true),
  ("recovery-keeps-minimization", "ChannelRecovered", chart, false)]

theorem casesExact :
    cases.all (fun (_, root, envelope, expected) =>
      admitted root envelope == expected) = true := by native_decide

theorem deniedPayloadNeverDelivered :
    syntheticDelivery "ChannelGoverned" chart = (false, []) ∧
    syntheticDelivery "ChannelGoverned" token =
      (true, [.verificationToken]) := by native_decide

theorem recoveryPreservesComposition :
    (model.compile "ChannelRecovered" == model.compile "ChannelGoverned") = true := by
  native_decide

theorem objectOriginsSurviveMix :
    ["VerificationHandoff", "SharedMemory"].all (fun owner =>
      ((model.compileWithProvenance "ChannelBase").toOption.get
        (by native_decide)).any (fun policy => policy.introducedBy == owner)) = true := by
  native_decide

theorem externalSubmitPolicyInherited :
    (match model.compile "ChannelGoverned" with
    | .error _ => false
    | .ok policies =>
        (isAuthorized
          (PriorAuthorizationExample.request
            { clinicalSeen := true, billingSeen := true, rawRecordIncluded := true }
            payerSubmit) entities policies).decision == .deny) = true := by
  native_decide

end CedarPooSpec.PriorAuthorizationInternalChannels
