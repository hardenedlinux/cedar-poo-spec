import CedarPooSpec.Functional.Compilation
import CedarPooSpec.PolicyJson

/-! Exercise every extension function and value constructor in Cedar Lean's
ExtFun/Ext definitions through the official Rust Cedar boundary. -/

namespace CedarPooSpec.ExtensionCoverageExample

open Cedar.Spec Cedar.Data CedarPooSpec.PolicyModules

def userType : EntityType := ⟨"User", []⟩
def docType : EntityType := ⟨"Document", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def alice : EntityUID := ⟨userType, "alice"⟩
def document : EntityUID := ⟨docType, "doc"⟩
def view : EntityUID := ⟨actionType, "view"⟩
def entityData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }
def entities : Entities := Map.make [
  (alice, entityData), (document, entityData), (view, entityData)]

def dec (s : String) : Expr := .call .decimal [.lit (.string s)]
def ip (s : String) : Expr := .call .ip [.lit (.string s)]
def dt (s : String) : Expr := .call .datetime [.lit (.string s)]
def dur (s : String) : Expr := .call .duration [.lit (.string s)]
def ctx (name : String) : Expr := .getAttr (.var .context) name
def eq (a b : Expr) : Expr := .binaryApp .eq a b

def all (checks : List Expr) : Expr :=
  checks.foldr Expr.and (.lit (.bool true))

def decimalChecks : Expr := all [
  eq (ctx "value") (dec "1.2500"),
  .call .lessThan [dec "1.2500", dec "2.0000"],
  .call .lessThanOrEqual [dec "2.0000", dec "2.0000"],
  .call .greaterThan [dec "2.0000", dec "1.2500"],
  .call .greaterThanOrEqual [dec "2.0000", dec "2.0000"]]

def ipChecks : Expr := all [
  eq (ctx "value") (ip "10.1.2.3"),
  .call .isIpv4 [ctx "value"],
  .unaryApp .not (.call .isIpv6 [ctx "value"]),
  .unaryApp .not (.call .isLoopback [ctx "value"]),
  .unaryApp .not (.call .isMulticast [ctx "value"]),
  .call .isInRange [ctx "value", ip "10.0.0.0/8"]]

def datetimeChecks : Expr := all [
  eq (ctx "value") (dt "2026-01-02T03:04:05.000Z"),
  eq (ctx "window") (dur "2h"),
  eq (.call .offset [ctx "value", ctx "window"])
    (dt "2026-01-02T05:04:05.000Z"),
  eq (.call .durationSince [ctx "value", dt "2026-01-02T01:04:05.000Z"])
    (dur "2h"),
  eq (.call .toDate [ctx "value"]) (dt "2026-01-02"),
  eq (.call .toTime [ctx "value"]) (dur "3h4m5s"),
  eq (.call .toMilliseconds [ctx "window"]) (.lit (.int 7200000)),
  eq (.call .toSeconds [ctx "window"]) (.lit (.int 7200)),
  eq (.call .toMinutes [ctx "window"]) (.lit (.int 120)),
  eq (.call .toHours [ctx "window"]) (.lit (.int 2)),
  eq (.call .toDays [ctx "window"]) (.lit (.int 0))]

def negativeDurationCheck : Expr :=
  eq (ctx "value") (dur "-2h")

def policy (id : String) (body : Expr) : Policy :=
  { id, effect := .permit,
    principalScope := .principalScope (.eq alice),
    actionScope := .actionScope (.eq view),
    resourceScope := .resourceScope (.eq document),
    condition := [{ kind := .when, body }] }

def model : Model := { modules := [
  { name := "Decimal", edits := [.extend (policy "decimal-functions" decimalChecks)] },
  { name := "IP", edits := [.extend (policy "ip-functions" ipChecks)] },
  { name := "Datetime", edits := [.extend (policy "datetime-functions" datetimeChecks)] },
  { name := "NegativeDuration", edits :=
      [.extend (policy "negative-duration" negativeDurationCheck)] }] }

/-- Compile-stage capability for this schema-free semantic fixture. -/
protected def program : CedarPooSpec.Functional.Compilation model :=
  CedarPooSpec.Functional.compilation model

def decimalValue : Value :=
  .ext (.decimal ((Cedar.Spec.Ext.Decimal.decimal "1.2500").get (by native_decide)))
def ipValue : Value :=
  .ext (.ipaddr ((Cedar.Spec.Ext.IPAddr.ip "10.1.2.3").get (by native_decide)))
def datetimeValue : Value :=
  .ext (.datetime ((Cedar.Spec.Ext.Datetime.parse "2026-01-02T03:04:05.000Z").get
    (by native_decide)))
def durationValue : Value :=
  .ext (.duration ((Cedar.Spec.Ext.Datetime.Duration.parse "2h").get
    (by native_decide)))
def datetimeOffsetValue : Value :=
  .ext (.datetime ((Cedar.Spec.Ext.Datetime.parse "2026-01-02T04:04:05+0100").get
    (by native_decide)))
def negativeDurationValue : Value :=
  .ext (.duration ((Cedar.Spec.Ext.Datetime.Duration.parse "-2h").get
    (by native_decide)))

def request (fields : List (String × Value)) : Request :=
  ⟨alice, view, document, Map.make fields⟩

def cases : List (String × String × Request × Decision) := [
  ("decimal-positive", "Decimal", request [("value", decimalValue)], .allow),
  ("decimal-negative", "Decimal", request [("value", .ext (.decimal
    ((Cedar.Spec.Ext.Decimal.decimal "1.2501").get (by native_decide))))], .deny),
  ("ip-positive", "IP", request [("value", ipValue)], .allow),
  ("ip-negative", "IP", request [("value", .ext (.ipaddr
    ((Cedar.Spec.Ext.IPAddr.ip "198.51.100.7").get (by native_decide))))], .deny),
  ("datetime-positive", "Datetime",
    request [("value", datetimeValue), ("window", durationValue)], .allow),
  ("datetime-offset-normalized", "Datetime",
    request [("value", datetimeOffsetValue), ("window", durationValue)], .allow),
  ("datetime-negative", "Datetime",
    request [("value", .ext (.datetime
      ((Cedar.Spec.Ext.Datetime.parse "2026-01-02T04:04:05.000Z").get
        (by native_decide)))), ("window", durationValue)], .deny),
  ("duration-negative-value", "NegativeDuration",
    request [("value", negativeDurationValue)], .allow)]

def decisionsExact
    (programContext : CedarPooSpec.Functional.Compilation CedarPooSpec.ExtensionCoverageExample.model :=
      CedarPooSpec.ExtensionCoverageExample.program) : Bool := cases.all fun (_, root, req, expected) =>
  match programContext.response root req entities with
  | .error _ => false
  | .ok response =>
      response.decision == expected && response.erroringPolicies.isEmpty

theorem decisionsExactFully : decisionsExact = true := by native_decide

end CedarPooSpec.ExtensionCoverageExample
