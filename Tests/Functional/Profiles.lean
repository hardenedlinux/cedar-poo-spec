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

/-- Exercise public consumers: present forged reads must not become admitted values. -/
def guards {Key : Type} {Value : Key → Type} [DecidableEq Key] [BEq Key]
    [LawfulBEq Key] [Hashable Key] (profile : Object.Memoized Key Value)
    (key : Key) (forged : Value key)
    (consume : Object.Memoized Key Value → Option (Value key)) : Bool :=
  let changed := profile.extendWith "Forged" do Object.Declaration.Builder.value key forged
  let missing : Except C4.Error (Object.Memoized Key Value) := Object.define "Missing" (pure ())
  (consume profile).isSome &&
    (changed.toOption.bind consume).isNone &&
    (missing.toOption.bind consume).isNone &&
    (changed.toOption.bind (fun object => object.read key)).isSome

private def policyProfile : PolicyProfile.Object String :=
  (PolicyProfile.define "Policy" "owned" (fun id => { Policy.allowAll with id })).toOption.get (by native_decide)

private def protectedProfile : Data.ProtectionProfile.Object :=
  (Data.ProtectionProfile.define "Protected" Data.ProtectedStorageFixture.baseIntent).toOption.get (by native_decide)

private def joined := AgenticAI.LanguageModel.Disclosure.joinedPrototype.toOption.get (by native_decide)

/-- One check inventory shared by kernel-facing tests and the native process. -/
def nativeChecks : List (String × Bool) := [
  ("policy", guards policyProfile .policy Policy.allowAll PolicyProfile.policy?),
  ("banking", guards MultiAccountBankingExample.transactionProfile .owner
    { MultiAccountBankingExample.transactionTemplate with actions := [] }
    Vertical.FinancialServices.BankingToolProfile.owner?),
  ("location", guards LakehouseGatewayExample.euProfile .boundary
    { LakehouseGatewayExample.euTemplate with inputKey := "substituted" }
    Data.Lakehouse.LocationProfile.boundary?),
  ("source", guards Cloud.Pipeline.GoogleThreatCase.productionProfile .control
    { Cloud.Pipeline.GoogleThreatCase.sourceControl with protectedBranch := "unprotected" }
    Cloud.Pipeline.SourceProfile.control?),
  ("protection", guards protectedProfile .intent
    { Data.ProtectedStorageFixture.baseIntent with keyVersion := "substituted" }
    Data.ProtectionProfile.intent?),
  ("controller", guards PaymentReleaseExample.controllerProfile .control
    { PaymentReleaseExample.controllerTemplate with amountAttribute := "substituted" }
    Vertical.FinancialServices.ControllerReleaseProfile.control?),
  ("disclosure", guards PriorAuthorizationInternalChannels.verificationProfile .channel
    { PriorAuthorizationInternalChannels.verificationTemplate with purposeKey := "substituted" }
    Vertical.Health.DisclosureProfile.channel?),
  ("handoff", guards AWS.ClaimSettlementHandoff.caseProfile .scope
    { AWS.ClaimSettlementHandoff.selected.scope with sourceRoot := "substituted" }
    Admission.Handoff.scope?),
  ("lineage", guards joined .artifact
    { AgenticAI.LanguageModel.Disclosure.joinedResult with digest := "substituted" }
    Data.LineageProfile.artifact?)]

example : nativeChecks.length = 9 ∧ nativeChecks.all Prod.snd = true := by native_decide

/-- Exercise actual public consumers in a compiled process; never return success
for an empty or partially checked family inventory. -/
def runNative : IO Unit := do
  unless nativeChecks.length == 9 do throw (IO.userError "profile family inventory changed")
  for (name, passed) in nativeChecks do
    unless passed do throw (IO.userError s!"native object profile failed: {name}")
    IO.println s!"OBJECT-PROFILE-NATIVE-OK {name} valid/forged/missing/actual-read"

open LeanPoo.Functional.ObjectContract Functional.ObjectProfile

/-- Both source and output-policy changes cannot conceal a changed hidden field. -/
private def doubleForged := PaymentReleaseExample.controllerProfile.extendWith "DoubleForged" do
  let control := { PaymentReleaseExample.controllerTemplate with amountAttribute := "substituted" }
  Object.Declaration.Builder.value .control control
  Object.Declaration.Builder.value .policy control.bounded
example : (doubleForged.toOption.bind Vertical.FinancialServices.ControllerReleaseProfile.policy?).isNone = true := by native_decide

private def changedSetting := policyProfile.extendWith "Child" do
  Object.Declaration.Builder.value .setting "child"
example : (changedSetting.toOption.bind PolicyProfile.policy?).map Policy.id = some "child" := by native_decide
example : (PolicyProfile.policy? policyProfile).map Policy.id = some "owned" := by native_decide

-- Missing capability resolution precedes observing this invalid object.
example : (prepare (PolicyProfile.contract (Setting := String)) (fun _ => none))
    = .error .check := by rfl

private def emptyBranch := Cloud.Pipeline.SourceProfile.onBranch
  Cloud.Pipeline.GoogleThreatCase.productionProfile "EmptyBranch" ""
example : (emptyBranch.toOption.bind Cloud.Pipeline.SourceProfile.control?).isNone = true := by native_decide

private def emptyKey := protectedProfile.extendWith "EmptyKey" do
  Object.Declaration.Builder.value .keyRef ""
example : (emptyKey.toOption.bind Data.ProtectionProfile.intent?).isNone = true := by native_decide

private def emptyLocation := LakehouseGatewayExample.euProfile.extendWith "EmptyLocation" do
  Object.Declaration.Builder.value .location ""
example : (emptyLocation.toOption.bind Data.Lakehouse.LocationProfile.boundary?).isNone = true := by native_decide

private def emptyDigest := joined.extendWith "EmptyDigest" do
  Object.Declaration.Builder.value .digest ""
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

open Lean in
run_cmd do
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  for declaration in [``Functional.ObjectProfile.coherent,
      ``Functional.ObjectProfile.prepare_missing,
      ``Functional.ObjectProfile.read_requires_contract,
      ``Functional.ObjectProfile.read_matches_projection,
      ``Functional.ObjectProfile.read_rejected,
      ``Functional.ObjectProfile.refinement_preserves_rejection] do
    for dependency in ← collectAxioms declaration do
      unless allowed.contains dependency.toString do
        throwError "Object Profile axiom boundary changed: {declaration}: {dependency}"
  logInfo "OBJECT-PROFILES-AXIOMS-OK six universal laws; nine object families"
end CedarPooSpec.FunctionalProfilesTest
