import Tests.Gateway.Fixture

namespace CedarPooSpec.GatewayTest
open Gateway.ProfileObject

def baseObject := define "GatewayProfile" profile
def extendedObject := baseObject.bind fun parent => extendChecks parent "StreamingProfile" ["revocation"]
def twiceExtendedObject := extendedObject.bind fun parent => extendChecks parent "ToolProfile" ["tool-result"]
-- Shared-base diamonds stay in one source family, with one declaration owner.
def auditObject := extendedObject.bind fun parent => parent.defineWith "AuditProfile" ["GatewayProfile"] do
  LeanPoo.Object.Dataflow.Builder.field .checks
    (.extend (.pure fun _ => fun inherited => inherited.map (· ++ ["audit"])))
def diamondObject := auditObject.bind fun parent =>
  parent.defineWith "AuditedStreamingProfile" ["StreamingProfile", "AuditProfile"] (pure ⟨⟩)
def duplicateFamilyMerge := extendedObject.bind fun streaming => auditObject.bind fun auditing =>
  streaming.defineFrom "DuplicateSharedBase" [auditing] (pure ⟨⟩)

private def admittedChecks (candidate : Except (LeanPoo.Object.Dataflow.Error Key) Object) :
    Option (List String) :=
  candidate.toOption.bind fun object =>
    (openSession profile object).toOption.bind fun session =>
      (session.read .profile).map (·.requiredChecks)

#guard admittedChecks baseObject == some ["source", "budget", "history"]
#guard admittedChecks extendedObject == some ["source", "budget", "history", "revocation"]
#guard admittedChecks twiceExtendedObject == some ["source", "budget", "history", "revocation", "tool-result"]
#guard admittedChecks diamondObject == some ["source", "budget", "history", "audit", "revocation"]
#guard match duplicateFamilyMerge with
  | .error (.schema (.duplicateNode "GatewayProfile")) => true
  | _ => false

-- Ordinary inherited slots can be replaced; the explicit Contract must refuse.
def strippedObject := baseObject.bind fun parent => parent.extendWith "StrippedProfile" do
  LeanPoo.Object.Dataflow.Builder.value .checks ["source"]
def reorderedObject := baseObject.bind fun parent => parent.extendWith "ReorderedProfile" do
  LeanPoo.Object.Dataflow.Builder.value .checks ["history", "budget", "source"]
def forgedProjection := baseObject.bind fun parent => parent.extendWith "ForgedProfile" do
  LeanPoo.Object.Dataflow.Builder.value .profile { profile with requiredChecks := ["source"] }
def renamedObject := baseObject.bind fun parent => parent.extendWith "RenamedProfile" do
  LeanPoo.Object.Dataflow.Builder.value .identity "other-profile"

#guard strippedObject.isOk && (admittedChecks strippedObject).isNone
#guard reorderedObject.isOk && (admittedChecks reorderedObject).isNone
#guard forgedProjection.isOk && (admittedChecks forgedProjection).isNone
#guard renamedObject.isOk && (admittedChecks renamedObject).isNone
#guard (admittedChecks (extendedObject.bind fun parent => extendChecks parent "Duplicate" ["budget"])).isNone
#guard admittedChecks baseObject == some profile.requiredChecks

-- The actual selected object feeds preparation, then actual Cedar admission.
def objectAdmission : Bool :=
  (extendedObject.toOption.bind fun object =>
    (openSession profile object).toOption.bind fun session =>
      (prepareFromObject model "base" schema context session request "invoke" true).toOption.bind fun value =>
        (Gateway.authorize value model "invoke" true context
          (value.profile.requiredChecks.map fun name => ⟨name, .satisfied⟩) entities).toOption.map
          (fun receipt => receipt.cedar.allowed)).getD false
#guard objectAdmission

#print axioms Gateway.ProfileObject.read_preserves_original_requirements
#print axioms Gateway.ProfileObject.inherited_obligations_are_satisfied
#print axioms Gateway.Profile.Refines.trans
#print axioms CedarPooSpec.Functional.ObjectProfile.materialized_source
#print axioms CedarPooSpec.Functional.ObjectProfile.materialized_read

end CedarPooSpec.GatewayTest
