import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.AWS.FinancialServices.Reconciliation.Reconciliation
import CedarPooSpec.Authorization.Compound

/-! A reviewable plan across the sample's ledger, notice, knowledge, Graph,
and write targets. Host facts stand for values the published REQUEST interceptor
loads from persistent storage. This pure example does not authenticate or
retrieve those facts, invoke a target, or establish transaction completion. -/

namespace CedarPooSpec.AWS.Reconciliation.Workflow

open Cedar.Spec CedarPooSpec.AWS.Reconciliation

/-- The interceptor checks the persisted proposal's reference and evidence
quality rather than trusting the agent's requested write arguments. -/
structure CaseRecord where
  proposedReference : String
  evidenceClean : Bool

/-- The source re-reads a human-approved draft and active contact at send time. -/
structure ApprovedDraft where
  recipient : String
  subject : String
  body : String
  approvedRevision : Nat
  currentRevision : Nat
  activeContact : Bool

structure MailCall where
  recipient : String
  subject : String
  body : String
  confirmationVerified : Bool

def investigationActions : List EntityUID :=
  [searchLedger, searchNotices, retrieve, searchCorrespondence]

def investigationAllowed
     (root : String)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AWS.Reconciliation.model CedarPooSpec.AWS.Reconciliation.schema :=
      CedarPooSpec.AWS.Reconciliation.program) : Bool :=
  match programContext.authorize root (investigationActions.map (readRequest agent)) entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

private def writeProvenanceAllowed (requestedReference : String)
    (caseRecord : Option CaseRecord) : Bool :=
  match caseRecord with
  | none => false
  | some record =>
      record.evidenceClean &&
        !record.proposedReference.isEmpty &&
        requestedReference == record.proposedReference

/-- Cedar evaluates confidence; the interceptor separately checks reference
and the stored evidence verdict. The caller must supply trusted host facts. -/
def autonomousWriteAllowed (root : String) (confidence : Option String)
    (requestedReference : String) (caseRecord : Option CaseRecord) : Bool :=
  decideAt root (writeRequest worker confidence) == some .allow &&
    writeProvenanceAllowed requestedReference caseRecord

private def approvedMailAllowed (call : MailCall)
    (draft : Option ApprovedDraft) : Bool :=
  call.confirmationVerified &&
    match draft with
    | none => false
    | some approved =>
        approved.activeContact &&
          approved.approvedRevision == approved.currentRevision &&
          call.recipient == approved.recipient &&
          call.subject == approved.subject &&
          call.body == approved.body

/-- Gateway policy alone allows this Graph action. The separate interceptor
requires verified confirmation, the approved revision, byte-exact text, and
an active recipient. -/
def mailAllowed (root : String) (call : MailCall)
    (draft : Option ApprovedDraft) : Bool :=
  decideAt root (readRequest platform graphSend) == some .allow &&
    approvedMailAllowed call draft

def routeRequests (confidence : Option String) : List Request :=
  investigationActions.map (readRequest agent) ++
    [writeRequest worker confidence, readRequest platform graphSend]

/-- A planned route crosses four read targets, a guarded ledger write, and
an approved Graph send. This Boolean represents admission checks only. -/
def routeAllowed
     (root : String) (confidence : Option String)
    (requestedReference : String) (caseRecord : Option CaseRecord)
    (mail : MailCall) (draft : Option ApprovedDraft)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.AWS.Reconciliation.model CedarPooSpec.AWS.Reconciliation.schema :=
      CedarPooSpec.AWS.Reconciliation.program) : Bool :=
  match programContext.authorize root (routeRequests confidence) entities with
  | .error _ => false
  | .ok receipt =>
      receipt.allowed &&
        writeProvenanceAllowed requestedReference caseRecord &&
        approvedMailAllowed mail draft

def cleanCase : CaseRecord := ⟨"draw-001", true⟩
def cleanDraft : ApprovedDraft :=
  ⟨"counterparty@example.org", "Draw update", "Confirmed", 3, 3, true⟩
def confirmedMail : MailCall :=
  ⟨"counterparty@example.org", "Draw update", "Confirmed", true⟩

theorem composedRouteAndOwnerVariants :
    routeAllowed "OwnerCombined" (some "85.0000") "draw-001"
      (some cleanCase) confirmedMail (some cleanDraft) = true ∧
    routeAllowed "Threshold90" (some "85.0000") "draw-001"
      (some cleanCase) confirmedMail (some cleanDraft) = false ∧
    routeAllowed "GraphPaused" (some "85.0000") "draw-001"
      (some cleanCase) confirmedMail (some cleanDraft) = false ∧
    routeAllowed "JointIncident" (some "90.0000") "draw-001"
      (some cleanCase) confirmedMail (some cleanDraft) = false ∧
    routeAllowed "Recovered" (some "85.0000") "draw-001"
      (some cleanCase) confirmedMail (some cleanDraft) = true := by
  native_decide

/-- The same Cedar permit can coexist with a wrong ledger reference or dirty
evidence; those are independent persistent-state checks. -/
theorem cedarAllowDoesNotProveWriteProvenance :
    decideAt "OwnerCombined" (writeRequest worker (some "90.0000")) = some .allow ∧
    autonomousWriteAllowed "OwnerCombined" (some "90.0000") "other-draw"
      (some cleanCase) = false ∧
    autonomousWriteAllowed "OwnerCombined" (some "90.0000") "draw-001"
      (some { cleanCase with evidenceClean := false }) = false ∧
    autonomousWriteAllowed "OwnerCombined" (some "90.0000") "draw-001"
      none = false := by
  native_decide

/-- The source intentionally excludes set_draw_status from model-offered
tools. If a compromised agent could call it with a high confidence input,
the Gateway policy alone would permit it. -/
theorem agentExposureRequiresSeparateBoundary :
    decideAt "OwnerCombined" (writeRequest agent (some "90.0000")) = some .allow := by
  native_decide

theorem cedarAllowDoesNotProveApprovedEmail :
    decideAt "OwnerCombined" (readRequest platform graphSend) = some .allow ∧
    mailAllowed "OwnerCombined"
      { confirmedMail with confirmationVerified := false } (some cleanDraft) = false ∧
    mailAllowed "OwnerCombined" confirmedMail
      (some { cleanDraft with currentRevision := 4 }) = false ∧
    mailAllowed "OwnerCombined" confirmedMail
      (some { cleanDraft with activeContact := false }) = false ∧
    mailAllowed "GraphPaused" confirmedMail (some cleanDraft) = false := by
  native_decide

end CedarPooSpec.AWS.Reconciliation.Workflow
