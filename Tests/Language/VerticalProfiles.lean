import Examples.Health.PriorAuthorization.InternalChannels
import Examples.Enterprise.Payment.PaymentRelease

/-! Typed industry objects must preserve existing contracts and affect actual
Cedar decisions after a child override, while the parent remains unchanged. -/
namespace CedarPooSpec.VerticalProfilesTest

open Cedar.Spec CedarPooSpec.Vertical.Health CedarPooSpec.Vertical.FinancialServices

namespace Health
open CedarPooSpec.PriorAuthorizationInternalChannels

def expectedMemory : DisclosureChannel :=
  { policyId := "write-shared-memory", action := remember,
    destination := memory, purpose := "resume-prior-authorization",
    payloadClass := "workflow-handle" }

example : verificationObject = verificationTemplate := by native_decide
example : memoryObject = expectedMemory := by native_decide
example : verificationPolicy = verificationTemplate.minimum := by native_decide
example : memoryPolicy = expectedMemory.minimum := by native_decide
example : memoryProfile.plan.precedence = ["MemoryChannel", "VerificationChannel"] := by
  native_decide
example : verificationProfile.read .purpose = some "verify-prior-authorization" ∧
    memoryProfile.read .purpose = some "resume-prior-authorization" := by native_decide
example : admitted "ChannelGoverned" token = true ∧
    admitted "ChannelGoverned" chart = false ∧
    admitted "ChannelGoverned" handle = true ∧
    admitted "MemoryRemoved" handle = false := by native_decide

def emptyPurpose : DisclosureProfile.Object :=
  (DisclosureProfile.onPurpose verificationProfile "EmptyPurpose" "").toOption.get
    (by native_decide)

def forgedPolicy : DisclosureProfile.Object :=
  (verificationProfile.extendWith "ForgedPolicy" do
    LeanPoo.Object.Declaration.Builder.value .policy Policy.allowAll).toOption.get
      (by native_decide)

def emptyPayload : DisclosureProfile.Object :=
  (DisclosureProfile.onPayload verificationProfile "EmptyPayload" "").toOption.get
    (by native_decide)

def forgedChannel : DisclosureProfile.Object :=
  (verificationProfile.extendWith "ForgedChannel" do
    LeanPoo.Object.Declaration.Builder.value .channel
      { verificationTemplate with purpose := "unrequested-purpose" }).toOption.get
        (by native_decide)

example : (DisclosureProfile.policy? emptyPurpose).isNone = true := by native_decide
example : (DisclosureProfile.policy? forgedPolicy).isNone = true := by native_decide
example : (DisclosureProfile.policy? emptyPayload).isNone = true := by native_decide
example : (DisclosureProfile.policy? forgedChannel).isNone = true := by native_decide
example : (DisclosureProfile.issues emptyPurpose).contains
    (.rejected [.purpose] "empty purpose") = true := by native_decide

-- An additional child contract cannot erase the inherited contract's refusal.
example (profile : DisclosureProfile.Object)
    (additional : DisclosureProfile.Object → List DisclosureProfile.Key →
      List (LeanPoo.Functional.ObjectContract.Issue DisclosureProfile.Key String))
    (rejected : LeanPoo.Functional.ObjectContract.diagnose
      DisclosureProfile.contract profile [] ≠ []) :
    LeanPoo.Functional.ObjectContract.diagnose
      (LeanPoo.Functional.ObjectContract.refine DisclosureProfile.contract additional)
      profile [] ≠ [] :=
  LeanPoo.Functional.ObjectContract.refine_preserves_rejection _ _ _ _ rejected
end Health

namespace Financial
open CedarPooSpec.PaymentReleaseExample

example : controllerRelease = controllerTemplate := by native_decide
example : controllerPolicy = controllerTemplate.bounded := by native_decide
example : restrictedControllerPolicy =
    ({ controllerTemplate with threshold := "200.0000" } : ControllerRelease).bounded := by
  native_decide
example : controllerProfile.read .threshold = some "500.0000" ∧
    restrictedControllerProfile.read .threshold = some "200.0000" ∧
    restrictedControllerProfile.read .controllerGroup = some controller ∧
    restrictedControllerProfile.read .seniorGroup = some senior := by native_decide
example : restrictedControllerProfile.plan.precedence =
    ["RestrictedControllerRelease", "ControllerRelease"] := by native_decide
example : authorized "Integrated" bob release small = true ∧
    authorized "Restricted" bob release small = false ∧
    authorized "Restricted" carol release small = true ∧
    authorized "Integrated" bob release small = true := by native_decide
example : (CedarPooSpec.PolicyJson.publish model "Restricted" schema).isOk = true := by
  native_decide

def invalidThreshold (text : String) : ControllerReleaseProfile.Object :=
  (ControllerReleaseProfile.withThreshold controllerProfile "InvalidThreshold" text).toOption.getD
    controllerProfile

example : ["not-decimal", "0.0000", "-1.0000"].all (fun text =>
    (ControllerReleaseProfile.policy? (invalidThreshold text)).isNone) = true := by
  native_decide
example : (ControllerReleaseProfile.policy? controllerProfile).isSome = true := by
  native_decide

def forgedControl : ControllerReleaseProfile.Object :=
  (controllerProfile.extendWith "ForgedControl" do
    LeanPoo.Object.Declaration.Builder.value .control
      { controllerTemplate with threshold := "99999.0000" }).toOption.get
        (by native_decide)

example : (ControllerReleaseProfile.policy? forgedControl).isNone = true := by native_decide
end Financial

end CedarPooSpec.VerticalProfilesTest
