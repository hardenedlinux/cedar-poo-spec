import Examples.Health.Pseudonymization.Deployment
import CedarPooSpec.Governance.ScopedApproval

/-!
A finite Host contract for one synthetic hospital lifecycle. The pure state
transition models an atomic ticket redemption; a deployed Host must make the
same checks and audit write durable before applying an external data effect.
-/

namespace CedarPooSpec.PseudonymizationExample.Lifecycle

open Cedar.Spec CedarPooSpec.PseudonymizationExample
open CedarPooSpec.Governance

inductive Step where
  | ingest | join | release | reidentify
  deriving BEq, Repr

structure Effect where
  step : Step
  actor : EntityUID
  source : EntityUID
  target : EntityUID
  purpose : String
  keyVersion : String
  payloadDigest : String
  iv : String := ""
  deriving BEq

structure State where
  epoch : Nat := 0
  policyRevision : Nat := 0
  approvalRevision : Nat := 0
  now : Nat := 0
  releaseBudget : Nat := 1
  ownerApproved : Bool := true
  authorizedKeys : List String := ["dek-v1"]
  auditAvailable : Bool := true
  usedIvs : List String := []
  auditLog : List String := []
  approvals : List ScopedApproval := []

structure Ticket where
  root : Deployment.Root
  policyRevision : Nat
  approvalRevision : Nat
  epoch : Nat
  effect : Effect
  deriving BEq

def Step.action : Step → EntityUID
  | .ingest => tokenize
  | .join => PseudonymizationExample.join
  | .release => releaseResult
  | .reidentify => PseudonymizationExample.reidentify

def Step.root : Step → Deployment.Root
  | .ingest | .join | .reidentify => .hospitalSiv
  | .release => .resultRelease

def Effect.root (effect : Effect) : Deployment.Root :=
  if effect.step == .ingest && effect.source == randomized then
    .randomizedGcm
  else effect.step.root

def authorizedApproval (state : State) (effect : Effect) : Bool :=
  state.approvals.any fun grant =>
    grant.approver == steward &&
    grant.applies effect.actor effect.step.action effect.purpose
      effect.source effect.target state.approvalRevision state.now

def facts (state : State) (effect : Effect) : Facts :=
  { targetDataset := effect.target,
    ownerApproved := state.ownerApproved,
    keyAuthorized := state.authorizedKeys.contains effect.keyVersion,
    requestedKeyVersion := effect.keyVersion,
    joinApproved := authorizedApproval state effect,
    releaseApproved := authorizedApproval state effect,
    reidentifyApproved := authorizedApproval state effect,
    budgetAvailable := state.releaseBudget > 0,
    auditReady := state.auditAvailable,
    ivUnique := !state.usedIvs.contains effect.iv }

def allowed (state : State) (effect : Effect) : Bool :=
  let req := request effect.actor effect.step.action effect.source (facts state effect)
  match program.authorize effect.root.name [req] entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

def prepare (state : State) (effect : Effect) : Option Ticket :=
  if effect.payloadDigest.isEmpty ||
      (effect.root == .randomizedGcm && effect.iv.isEmpty) ||
      !allowed state effect then none
  else some ⟨effect.root, state.policyRevision,
    state.approvalRevision, state.epoch, effect⟩

/-- The return value is a modeled state transition, not a record that an
    external encryption, query, or plaintext release actually took place. -/
def redeem (state : State) (ticket : Ticket) (effect : Effect) : Option State :=
  if ticket.root != effect.root ||
      ticket.policyRevision != state.policyRevision ||
      ticket.approvalRevision != state.approvalRevision ||
      ticket.epoch != state.epoch || ticket.effect != effect ||
      !allowed state effect then none
  else
    let next := { state with epoch := state.epoch + 1, auditLog := state.auditLog ++ [effect.payloadDigest] }
    let next := if effect.step == .release then
      { next with releaseBudget := state.releaseBudget - 1 }
      else next
    let next := if effect.step == .ingest && effect.iv != "" then
      { next with usedIvs := effect.iv :: state.usedIvs }
      else next
    some next

def revoke (state : State) : State :=
  { state with approvalRevision := state.approvalRevision + 1, epoch := state.epoch + 1 }

def grant (actor operation : EntityUID) (purpose : String)
    (source target : EntityUID) : ScopedApproval :=
  { id := purpose, approver := steward, actor, operation, purpose,
    source, target, revision := 0, expiresAt := 10 }

def initial : State :=
  { now := 1, approvals := [
      grant agent PseudonymizationExample.join "study-one" hospital hospital,
      grant agent releaseResult "study-one" hospital hospital,
      grant steward PseudonymizationExample.reidentify "clinical-emergency" hospital hospital] }

def ingestEffect : Effect :=
  { step := .ingest, actor := ingest, source := hospital, target := hospital,
    purpose := "hospital-ingestion", keyVersion := "dek-v1", payloadDigest := "record-1" }
def joinEffect : Effect :=
  { step := .join, actor := agent, source := hospital, target := hospital,
    purpose := "study-one", keyVersion := "dek-v1", payloadDigest := "query-1" }
def releaseEffect : Effect :=
  { step := .release, actor := agent, source := hospital, target := hospital,
    purpose := "study-one", keyVersion := "dek-v1", payloadDigest := "result-1" }
def revealEffect : Effect :=
  { step := .reidentify, actor := steward, source := hospital, target := hospital,
    purpose := "clinical-emergency", keyVersion := "dek-v1", payloadDigest := "reveal-1" }
def gcmEffect : Effect :=
  { step := .ingest, actor := ingest, source := randomized, target := randomized,
    purpose := "randomized-ingestion", keyVersion := "dek-v1",
    payloadDigest := "record-gcm-1", iv := "iv-1" }

def step (state : State) (effect : Effect) : Option State := do
  let ticket ← prepare state effect
  redeem state ticket effect

def lifecycle : Option State := do
  let ingested ← step initial ingestEffect
  let joined ← step ingested joinEffect
  let released ← step joined releaseEffect
  step released revealEffect

theorem lifecycleConsumesOneReleaseAndAuditsFourSteps :
    (lifecycle.map fun state =>
      (state.epoch, state.releaseBudget, state.auditLog.length)) =
      some (4, 0, 4) := by native_decide

theorem swappedDatasetCannotRedeem :
    ((prepare initial joinEffect).bind fun ticket =>
      redeem initial ticket { joinEffect with target := research }) = none := by
  native_decide

theorem swappedActorAndTargetCannotUseApproval :
    prepare initial { joinEffect with actor := operator } = none ∧
    prepare initial { joinEffect with target := research } = none := by
  native_decide

theorem concurrentTicketsCannotBothRedeem :
    ((prepare initial joinEffect).bind fun first =>
      (prepare initial joinEffect).bind fun second =>
        (redeem initial first joinEffect).bind fun afterFirst =>
          redeem afterFirst second joinEffect) = none := by
  native_decide

theorem revokedApprovalCannotRedeem :
    ((prepare initial joinEffect).bind fun ticket =>
      redeem (revoke initial) ticket joinEffect) = none := by
  native_decide

theorem policyRevisionInvalidatesTicket :
    ((prepare initial joinEffect).bind fun ticket =>
      redeem { initial with policyRevision := 1 } ticket joinEffect) = none := by
  native_decide

theorem expiredAndWrongPurposeCannotPrepare :
    prepare { initial with now := 10 } joinEffect = none ∧
    prepare initial { joinEffect with purpose := "other-study" } = none := by
  native_decide

theorem ownerOrKeyWithdrawalBlocksNewOperation :
    prepare { initial with ownerApproved := false } joinEffect = none ∧
    prepare { initial with authorizedKeys := [] } ingestEffect = none := by
  native_decide

theorem auditFailurePreventsPlaintextTransition :
    step { initial with auditAvailable := false } revealEffect = none := by
  native_decide

theorem resultBudgetCannotBeReused :
    ((step initial releaseEffect).bind fun state => step state releaseEffect) = none := by
  native_decide

theorem gcmIvMustBeAllocatedOnce :
    prepare initial { gcmEffect with iv := "" } = none ∧
    ((step initial gcmEffect).bind fun state => step state gcmEffect) = none ∧
    ((step initial gcmEffect).bind fun state =>
      step state { gcmEffect with iv := "iv-2" }).isSome = true := by
  native_decide

end CedarPooSpec.PseudonymizationExample.Lifecycle
