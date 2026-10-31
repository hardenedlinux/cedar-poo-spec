import CedarPooSpec.PolicyModules

/-!
One controller-owned payment release slot. A consumer supplies its actual
group, action, resource scope, field names, and decimal threshold. Cedar
checks the projected facts; the Host binds the decision to the payment state.
-/

namespace CedarPooSpec.Vertical.FinancialServices

open Cedar.Spec CedarPooSpec.PolicyModules

structure ControllerRelease where
  policyId : PolicyID
  action : EntityUID
  controllerGroup : EntityUID
  seniorGroup : EntityUID
  resourceScope : ResourceScope
  threshold : String
  amountAttribute : String := "amount"
  matchedAttribute : String := "matched"
  deriving DecidableEq

private def field (name : String) : Expr :=
  .getAttr (.var .resource) name

def ControllerRelease.broad (control : ControllerRelease) : Policy :=
  { id := control.policyId, effect := .permit,
    principalScope := .principalScope (.mem control.controllerGroup),
    actionScope := .actionScope (.eq control.action),
    resourceScope := control.resourceScope,
    condition := [{ kind := .when, body := .lit (.bool true) }] }

def ControllerRelease.bounded (control : ControllerRelease) : Policy :=
  let withinThreshold : Expr :=
    .call .lessThanOrEqual
      [field control.amountAttribute, .call .decimal [.lit (.string control.threshold)]]
  let senior : Expr :=
    .binaryApp .mem (.var .principal) (.lit (.entityUID control.seniorGroup))
  let body : Expr :=
    .and (field control.matchedAttribute) (.or withinThreshold senior)
  { control.broad with condition := [{ kind := .when, body }] }

def ControllerRelease.introduce (control : ControllerRelease) : Edit :=
  .extend control.broad

def ControllerRelease.strengthen (control : ControllerRelease) : Edit :=
  .overlay control.bounded

def ControllerRelease.withdraw (control : ControllerRelease) : Edit :=
  .remove control.policyId

end CedarPooSpec.Vertical.FinancialServices
