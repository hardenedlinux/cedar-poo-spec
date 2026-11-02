import CedarPooSpec.PolicyModules

/-!
A healthcare disclosure channel whose purpose and payload class can be
strengthened without copying its broad permit. The Host supplies the request
context from the actual disclosure; Cedar checks its value and entity scopes.
Patient identity and delegation revocation remain independent controls.
-/

namespace CedarPooSpec.Vertical.Health

open Cedar.Spec CedarPooSpec.PolicyModules

structure DisclosureChannel where
  policyId : PolicyID
  action : EntityUID
  destination : EntityUID
  purpose : String
  payloadClass : String
  purposeKey : String := "purpose"
  payloadClassKey : String := "payloadClass"
  patientMatchKey : String := "patientMatches"
  delegationKey : String := "delegationActive"
  deriving DecidableEq

def DisclosureChannel.broad (channel : DisclosureChannel) : Policy :=
  { id := channel.policyId, effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq channel.action),
    resourceScope := .resourceScope (.eq channel.destination),
    condition := [{ kind := .when, body := .lit (.bool true) }] }

private def context (key : String) : Expr := .getAttr (.var .context) key
private def equalsString (key value : String) : Expr :=
  .binaryApp .eq (context key) (.lit (.string value))

def DisclosureChannel.minimum (channel : DisclosureChannel) : Policy :=
  let body : Expr :=
    .and (equalsString channel.purposeKey channel.purpose)
      (.and (equalsString channel.payloadClassKey channel.payloadClass)
        (.and (context channel.patientMatchKey)
          (.hasAttr (.var .context) channel.delegationKey)))
  { channel.broad with condition := [{ kind := .when, body }] }

def DisclosureChannel.introduce (channel : DisclosureChannel) : Edit :=
  .extend channel.broad

def DisclosureChannel.strengthen (channel : DisclosureChannel) : Edit :=
  .overlay channel.minimum

def DisclosureChannel.withdraw (channel : DisclosureChannel) : Edit :=
  .remove channel.policyId

end CedarPooSpec.Vertical.Health
