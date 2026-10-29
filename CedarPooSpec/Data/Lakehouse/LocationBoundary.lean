import CedarPooSpec.PolicyModules

/-!
A lakehouse data-location boundary over a projected request input. The
consumer chooses the Cedar scopes and the authenticated input field. This
object does not infer geography, query data, or enforce downstream row rules.
-/

namespace CedarPooSpec.Data.Lakehouse

open Cedar.Spec CedarPooSpec.PolicyModules

structure LocationBoundary where
  policyId : PolicyID
  principalScope : PrincipalScope
  actionScope : ActionScope
  resourceScope : ResourceScope
  deniedLocation : String
  inputKey : String := "input"
  locationKey : String := "geography"
  denyMissing : Bool := false
  deriving DecidableEq

def LocationBoundary.input (boundary : LocationBoundary) : Expr :=
  .getAttr (.var .context) boundary.inputKey

def LocationBoundary.present (boundary : LocationBoundary) : Expr :=
  .hasAttr boundary.input boundary.locationKey

def LocationBoundary.location (boundary : LocationBoundary) : Expr :=
  .getAttr boundary.input boundary.locationKey

def LocationBoundary.matches (boundary : LocationBoundary) : Expr :=
  .and boundary.present
    (.binaryApp .eq boundary.location (.lit (.string boundary.deniedLocation)))

def LocationBoundary.blocked (boundary : LocationBoundary) : Expr :=
  if boundary.denyMissing then
    .or (.unaryApp .not boundary.present) boundary.matches
  else boundary.matches

def LocationBoundary.policy (boundary : LocationBoundary) : Policy :=
  { id := boundary.policyId, effect := .forbid,
    principalScope := boundary.principalScope,
    actionScope := boundary.actionScope,
    resourceScope := boundary.resourceScope,
    condition := [{ kind := .when, body := boundary.blocked }] }

def LocationBoundary.introduce (boundary : LocationBoundary) : Edit :=
  .extend boundary.policy

def LocationBoundary.revise (boundary : LocationBoundary) : Edit :=
  .overlay boundary.policy

def LocationBoundary.withdraw (boundary : LocationBoundary) : Edit :=
  .remove boundary.policyId

end CedarPooSpec.Data.Lakehouse
