import CedarPooSpec.Vertical.Health.DisclosureChannel
import LeanPoo.Object.Dataflow
import CedarPooSpec.Functional.ObjectProfile

/-! Typed disclosure configuration. Inherited channel and policy slots read
final self; a child changes only the industry fields it owns. -/
namespace CedarPooSpec.Vertical.Health.DisclosureProfile
open LeanPoo.Object.Dataflow (Expr)

open Cedar.Spec LeanPoo
open LeanPoo.Object.Dataflow.Builder

inductive Key where
  | template
  | policyId | action | destination | purpose | payloadClass | channel | policy
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .template => DisclosureChannel
  | .policyId => PolicyID
  | .action | .destination => EntityUID
  | .purpose | .payloadClass => String
  | .channel => DisclosureChannel
  | .policy => Policy

abbrev Object := LeanPoo.Object.Dataflow.Instance Key Value

def define (name : String) (initial : DisclosureChannel) : Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  LeanPoo.Object.Dataflow.define name do
    LeanPoo.Object.Dataflow.Builder.value .template initial
    value .policyId initial.policyId
    value .action initial.action
    value .destination initial.destination
    value .purpose initial.purpose
    value .payloadClass initial.payloadClass
    derived .channel
      ((fun policyId action destination purpose payloadClass => { initial with policyId, action, destination, purpose, payloadClass })
        <$> Expr.need (Value := Value) .policyId
        <*> Expr.need (Value := Value) .action
        <*> Expr.need (Value := Value) .destination
        <*> Expr.need (Value := Value) .purpose
        <*> Expr.need (Value := Value) .payloadClass)
    derived .policy (DisclosureChannel.minimum
        <$> Expr.need (Value := Value) .channel)

def onPurpose (parent : Object) (name purpose : String) : Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  parent.extendWith name do value .purpose purpose

def onPayload (parent : Object) (name payloadClass : String) : Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  parent.extendWith name do value .payloadClass payloadClass

open LeanPoo.Functional.ObjectContract

/-- Slot values are statically indexed by Key. The structural contract checks
actual inventory/presence; no dynamic value cast or second type checker exists. -/
private def shape : Contract Object Key Unit String :=
  Functional.ObjectProfile.shape [.template, .policyId, .action, .destination, .purpose, .payloadClass, .channel, .policy]
/-- The industry refinement must also hold after inherited computation or an
explicit override. A forged derived channel/policy cannot bypass its inputs. -/
def contract : Contract Object Key Unit String :=
  refine shape fun profile path =>
    match profile.read .channel, profile.read .policy with
    | some channel, some policy =>
        let empty :=
          (if channel.purpose.isEmpty then [.rejected (path ++ [.purpose]) "empty purpose"] else []) ++
          (if channel.payloadClass.isEmpty then [.rejected (path ++ [.payloadClass]) "empty payload class"] else [])
        let templateAligned := match profile.read .template with
          | none => false
          | some template => decide (channel = { template with
              policyId := channel.policyId, action := channel.action, destination := channel.destination,
              purpose := channel.purpose, payloadClass := channel.payloadClass })
        let aligned := templateAligned = true ∧ profile.read .policyId = some channel.policyId ∧
          profile.read .action = some channel.action ∧
          profile.read .destination = some channel.destination ∧
          profile.read .purpose = some channel.purpose ∧
          profile.read .payloadClass = some channel.payloadClass ∧ policy = channel.minimum
        empty ++ (if aligned then [] else [.rejected path "disclosure projection mismatch"])
    | _, _ => [.rejected path "missing disclosure projection"]

def issues (profile : Object) : List (Issue Key String) := diagnose contract profile []

def channel? (profile : Object) : Option DisclosureChannel :=
  Functional.ObjectProfile.read contract profile .channel

def policy? (profile : Object) : Option Policy :=
  Functional.ObjectProfile.read contract profile .policy

theorem policy_requires_contract (profile : Object) (policy : Policy)
    (accepted : policy? profile = some policy) : diagnose contract profile [] = [] :=
  Functional.ObjectProfile.read_requires_contract contract profile _ _ accepted

end CedarPooSpec.Vertical.Health.DisclosureProfile
