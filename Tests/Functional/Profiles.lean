import Tests.Functional.ProfileWorkloads
import CedarPooSpec.PolicyProfile
import CedarPooSpec.Functional.ObjectProfile
import Examples.Enterprise.AWS.FinancialServices.MultiAccountBanking.MultiAccountBanking
import Examples.Enterprise.AWS.FinancialServices.LakehouseGateway.LakehouseGateway
import Examples.Enterprise.AWS.FinancialServices.ClaimSettlementHandoff
import Examples.Cloud.Pipeline.GoogleThreatCase
import Examples.Health.AgenticAI.LanguageModel.Disclosure
import Examples.Health.PriorAuthorization.InternalChannels
import Examples.Enterprise.Payment.PaymentRelease
import Productions.Data.ProtectedStorageFixture
import CedarPooSpec.Data.ProtectionProfile
import Lean

namespace CedarPooSpec.FunctionalProfilesTest
open Cedar.Spec LeanPoo CedarPooSpec

/-- Actual materializer work is checked for every domain, including shared dependencies. -/
private def materializesOnce {Key : Type} {Value : Key → Type} [DecidableEq Key] [BEq Key]
    [LawfulBEq Key] [Hashable Key] (profile : Object.Dataflow.Instance Key Value) : Bool :=
  match profile.template.build with
  | .error _ => false
  | .ok (object,evaluated) =>
    evaluated.length == profile.template.graph.keys.length &&
    profile.template.graph.keys.all (fun key => evaluated.count key == 1) &&
    object.slotNames == profile.slotNames

/-- Exercise public consumers: present forged reads must not become admitted values. -/
def guards {Key : Type} {Value : Key → Type} [DecidableEq Key] [BEq Key]
    [LawfulBEq Key] [Hashable Key] (profile : Object.Dataflow.Instance Key Value)
    (key : Key) (forged : Value key)
    (consume : Object.Dataflow.Instance Key Value → Option (Value key)) : Bool :=
  let changed := profile.extendWith "Forged" do Object.Dataflow.Builder.value key forged
  let missing : Except (Object.Dataflow.Error Key) (Object.Dataflow.Instance Key Value) := Object.Dataflow.define "Missing" (pure ⟨⟩)
  materializesOnce profile && missing.isOk && (consume profile).isSome &&
    (changed.toOption.bind consume).isNone &&
    (missing.toOption.bind consume).isNone &&
    (changed.toOption.bind (fun object => object.read key)).isSome

private def policyProfile : PolicyProfile.Object String :=
  (PolicyProfile.define "Policy" "owned" (fun id => { Policy.allowAll with id })).toOption.get (by native_decide)

private def protectedProfile : Data.ProtectionProfile.Object :=
  (Data.ProtectionProfile.define "Protected" Data.ProtectedStorageFixture.baseIntent).toOption.get (by native_decide)

private def joined := AgenticAI.LanguageModel.Disclosure.joinedPrototype.toOption.get (by native_decide)

/-- One check inventory shared by kernel-facing tests and the native process. -/
def probes : List FunctionalProfileWorkloads.Probe := [
  { name := "policy", guards := (guards policyProfile .policy Policy.allowAll PolicyProfile.policy?),
    fields := (LeanPoo.allSlots policyProfile.plan).length,
    consume := (FunctionalProfileWorkloads.consume PolicyProfile.contract policyProfile .policy Policy.allowAll) },
  { name := "banking", guards := (guards MultiAccountBankingExample.transactionProfile .owner
    { MultiAccountBankingExample.transactionTemplate with actions := [] }
    Vertical.FinancialServices.BankingToolProfile.owner?),
    fields := (LeanPoo.allSlots MultiAccountBankingExample.transactionProfile.plan).length,
    consume := (FunctionalProfileWorkloads.consume Vertical.FinancialServices.BankingToolProfile.contract MultiAccountBankingExample.transactionProfile .owner
    { MultiAccountBankingExample.transactionTemplate with actions := [] }) },
  { name := "location", guards := (guards LakehouseGatewayExample.euProfile .boundary
    { LakehouseGatewayExample.euTemplate with inputKey := "substituted" }
    Data.Lakehouse.LocationProfile.boundary?),
    fields := (LeanPoo.allSlots LakehouseGatewayExample.euProfile.plan).length,
    consume := (FunctionalProfileWorkloads.consume Data.Lakehouse.LocationProfile.contract LakehouseGatewayExample.euProfile .boundary
    { LakehouseGatewayExample.euTemplate with inputKey := "substituted" }) },
  { name := "source", guards := (guards Cloud.Pipeline.GoogleThreatCase.productionProfile .control
    { Cloud.Pipeline.GoogleThreatCase.sourceControl with protectedBranch := "unprotected" }
    Cloud.Pipeline.SourceProfile.control?),
    fields := (LeanPoo.allSlots Cloud.Pipeline.GoogleThreatCase.productionProfile.plan).length,
    consume := (FunctionalProfileWorkloads.consume Cloud.Pipeline.SourceProfile.contract Cloud.Pipeline.GoogleThreatCase.productionProfile .control
    { Cloud.Pipeline.GoogleThreatCase.sourceControl with protectedBranch := "unprotected" }) },
  { name := "protection", guards := (guards protectedProfile .intent
    { Data.ProtectedStorageFixture.baseIntent with keyVersion := "substituted" }
    Data.ProtectionProfile.intent?),
    fields := (LeanPoo.allSlots protectedProfile.plan).length,
    consume := (FunctionalProfileWorkloads.consume Data.ProtectionProfile.contract protectedProfile .intent
    { Data.ProtectedStorageFixture.baseIntent with keyVersion := "substituted" }) },
  { name := "controller", guards := (guards PaymentReleaseExample.controllerProfile .control
    { PaymentReleaseExample.controllerTemplate with amountAttribute := "substituted" }
    Vertical.FinancialServices.ControllerReleaseProfile.control?),
    fields := (LeanPoo.allSlots PaymentReleaseExample.controllerProfile.plan).length,
    consume := (FunctionalProfileWorkloads.consume Vertical.FinancialServices.ControllerReleaseProfile.contract PaymentReleaseExample.controllerProfile .control
    { PaymentReleaseExample.controllerTemplate with amountAttribute := "substituted" }) },
  { name := "disclosure", guards := (guards PriorAuthorizationInternalChannels.verificationProfile .channel
    { PriorAuthorizationInternalChannels.verificationTemplate with purposeKey := "substituted" }
    Vertical.Health.DisclosureProfile.channel?),
    fields := (LeanPoo.allSlots PriorAuthorizationInternalChannels.verificationProfile.plan).length,
    consume := (FunctionalProfileWorkloads.consume Vertical.Health.DisclosureProfile.contract PriorAuthorizationInternalChannels.verificationProfile .channel
    { PriorAuthorizationInternalChannels.verificationTemplate with purposeKey := "substituted" }) },
  { name := "handoff", guards := (guards AWS.ClaimSettlementHandoff.caseProfile .scope
    { AWS.ClaimSettlementHandoff.selected.scope with sourceRoot := "substituted" }
    Admission.Handoff.scope?),
    fields := (LeanPoo.allSlots AWS.ClaimSettlementHandoff.caseProfile.plan).length,
    consume := (FunctionalProfileWorkloads.consume Admission.Handoff.contract AWS.ClaimSettlementHandoff.caseProfile .scope
    { AWS.ClaimSettlementHandoff.selected.scope with sourceRoot := "substituted" }) },
  { name := "lineage", guards := (guards joined .artifact
    { AgenticAI.LanguageModel.Disclosure.joinedResult with digest := "substituted" }
    Data.LineageProfile.artifact?),
    fields := (LeanPoo.allSlots joined.plan).length,
    consume := (FunctionalProfileWorkloads.consume Data.LineageProfile.contract joined .artifact
    { AgenticAI.LanguageModel.Disclosure.joinedResult with digest := "substituted" }) }]

def nativeChecks : List (String × Bool) := probes.map fun probe => (probe.name, probe.guards)

example : nativeChecks.length = 9 ∧ nativeChecks.all Prod.snd = true := by native_decide

/-- Exercise actual public consumers in a compiled process; never return success
for an empty or partially checked family inventory. -/
def runNative : IO Unit := do
  unless nativeChecks.length == 9 do throw (IO.userError "profile family inventory changed")
  for (name, passed) in nativeChecks do
    unless passed do throw (IO.userError s!"native object profile failed: {name}")
    IO.println s!"OBJECT-PROFILE-NATIVE-OK {name} valid/forged/missing/actual-read"

def runWorkloads (selected : Option String) : IO Unit := do
  let chosen := probes.filter fun probe => selected.isNone || selected == some probe.name
  unless chosen.length == (if selected.isNone then 9 else 1) do
    throw (IO.userError "unknown or incomplete native profile selection")
  for probe in chosen do FunctionalProfileWorkloads.run probe

open LeanPoo.Functional.ObjectContract Functional.ObjectProfile

/-- Both source and output-policy changes cannot conceal a changed hidden field. -/
private def doubleForged := PaymentReleaseExample.controllerProfile.extendWith "DoubleForged" do
  let control := { PaymentReleaseExample.controllerTemplate with amountAttribute := "substituted" }
  Object.Dataflow.Builder.value .control control
  Object.Dataflow.Builder.value .policy control.bounded
example : (doubleForged.toOption.bind Vertical.FinancialServices.ControllerReleaseProfile.policy?).isNone = true := by native_decide

private def changedSetting := policyProfile.extendWith "Child" do
  Object.Dataflow.Builder.value .setting "child"
example : (changedSetting.toOption.bind PolicyProfile.policy?).map Policy.id = some "child" := by native_decide
example : (PolicyProfile.policy? policyProfile).map Policy.id = some "owned" := by native_decide

-- Missing capability resolution precedes observing this invalid object.
example : (prepare (PolicyProfile.contract (Setting := String)) (fun _ => none))
    = .error .check := by rfl

private def emptyBranch := Cloud.Pipeline.SourceProfile.onBranch
  Cloud.Pipeline.GoogleThreatCase.productionProfile "EmptyBranch" ""
example : (emptyBranch.toOption.bind Cloud.Pipeline.SourceProfile.control?).isNone = true := by native_decide

private def emptyKey := protectedProfile.extendWith "EmptyKey" do
  Object.Dataflow.Builder.value .keyRef ""
example : (emptyKey.toOption.bind Data.ProtectionProfile.intent?).isNone = true := by native_decide

private def emptyLocation := LakehouseGatewayExample.euProfile.extendWith "EmptyLocation" do
  Object.Dataflow.Builder.value .location ""
example : (emptyLocation.toOption.bind Data.Lakehouse.LocationProfile.boundary?) =
    some { LakehouseGatewayExample.euTemplate with deniedLocation := "" } := by native_decide

/-- An explicit empty boundary value is distinct from an absent geography field. -/
private def emptyLocationDecisions : Bool :=
  let boundary := { LakehouseGatewayExample.euTemplate with deniedLocation := "" }
  let policies := [{ Policy.allowAll with id := "baseline" }, boundary.policy]
  let evaluate := fun location => isAuthorized
    (LakehouseGatewayExample.request LakehouseGatewayExample.adjusterUS
      LakehouseGatewayExample.queryClaims location) LakehouseGatewayExample.entities policies
  (evaluate (some "")).decision == .deny &&
    (evaluate (some "EU")).decision == .allow &&
    (evaluate none).decision == .allow &&
    [some "", some "EU", none].all (fun location => (evaluate location).erroringPolicies.isEmpty)
example : emptyLocationDecisions = true := by native_decide

private def emptyDigest := joined.extendWith "EmptyDigest" do
  Object.Dataflow.Builder.value .digest ""
example : (emptyDigest.toOption.bind Data.LineageProfile.artifact?).isNone = true := by native_decide

-- Withdrawing all actions is a legitimate paused owner, not malformed configuration.
private def pausedAll := Vertical.FinancialServices.BankingToolProfile.onActions
  MultiAccountBankingExample.transactionProfile "PausedAll" []
example : (pausedAll.toOption.bind Vertical.FinancialServices.BankingToolProfile.owner?).isSome = true := by native_decide

private def refusingProvider (owner : String) : Operations (PolicyProfile.contract (Setting := String))
  | .check => if owner == "Profile" then
      some (fun _ => .error [.rejected [] "specialized refusal"])
    else providers PolicyProfile.contract owner .check
  | .project => providers PolicyProfile.contract owner .project

private def specializedRefusal : Bool :=
  match prepare PolicyProfile.contract
      (LeanPoo.Functional.assemble Functional.ObjectProfile.order refusingProvider) with
  | .error _ => false
  | .ok factory => match factory policyProfile with
    | .ok _ => false
    | .error issues => issues == [.rejected [] "specialized refusal"]
example : specializedRefusal = true := by native_decide

private def onlyCheck : Operations (PolicyProfile.contract (Setting := String))
  | .check => some (fun _ => .error [.rejected [] "must not observe yet"])
  | .project => none
example : prepare PolicyProfile.contract onlyCheck = .error .project := by rfl

-- These elaboration checks fail only if a wrong typed value/index is accepted.
example : True := by
  fail_if_success
    have _ : PolicyProfile.Value String .render := fun (_ : Nat) => Policy.allowAll
  trivial
example : True := by
  fail_if_success
    have _ : Data.LineageProfile.Value .sources := ("untyped sources" : String)
  trivial
example : True := by
  fail_if_success
    have _ : Data.ProtectionProfile.Value .storage := ("storage name" : String)
  trivial
example (first _second : PolicyProfile.Object String)
    (_checked : Checked PolicyProfile.contract first) : True := by
  fail_if_success
    have _ : Checked PolicyProfile.contract _second := _checked
  trivial
example (profile : PolicyProfile.Object String)
    (left _right : Check PolicyProfile.Key (PolicyProfile.Value String))
    (_checked : Checked left profile) : True := by
  fail_if_success
    have _ : Checked _right profile := _checked
  trivial

example (contract : Functional.ObjectProfile.Check PolicyProfile.Key (PolicyProfile.Value String))
    (profile : PolicyProfile.Object String)
    (left _right : LeanPoo.Functional.Factory (PolicyProfile.Object String)
      (fun object => Except (List (LeanPoo.Functional.ObjectContract.Issue PolicyProfile.Key String))
        (Functional.ObjectProfile.Access contract object)))
    (_session : Functional.ObjectProfile.Session contract left profile) : True := by
  fail_if_success
    have _ : Functional.ObjectProfile.Session contract _right profile := _session
  trivial

open Lean in
run_cmd do
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  for declaration in [``Functional.prepareDiagnostics_exact,
      ``Functional.ObjectProfile.coherent,
      ``Functional.ObjectProfile.materialized_read,
      ``Functional.ObjectProfile.materialized_inventory,
      ``Functional.ObjectProfile.materialized_source,
      ``Functional.ObjectProfile.materialized_lowering,
      ``Functional.ObjectProfile.standard_eq_assemble,
      ``Functional.prepareProgram_retained,
      ``Functional.ObjectProfile.admit_read_eq,
      ``Functional.ObjectProfile.Access.read_matches,
      ``Functional.ObjectProfile.Access.accepted,
      ``Functional.ObjectProfile.Session.read_matches,
      ``Functional.ObjectProfile.Session.no_session_if_refused,
      ``Functional.ObjectProfile.prepare_missing,
      ``Functional.ObjectProfile.read_requires_contract,
      ``Functional.ObjectProfile.read_matches_projection,
      ``Functional.ObjectProfile.read_rejected,
      ``Functional.ObjectProfile.refinement_preserves_rejection] do
    for dependency in ← collectAxioms declaration do
      unless allowed.contains dependency.toString do
        throwError "Object Profile axiom boundary changed: {declaration}: {dependency}"
  logInfo "OBJECT-PROFILES-AXIOMS-OK eighteen universal laws; nine object families"
end CedarPooSpec.FunctionalProfilesTest
