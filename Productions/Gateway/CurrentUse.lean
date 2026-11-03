import CedarPooSpec.SchemaJson
import CedarPooSpec.Gateway.ZeroTrust
import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Vertical.Health.DisclosureProfile
import CedarPooSpec.Vertical.FinancialServices.ControllerReleaseProfile

/-! Production-owned composition vectors, not deployed Host credentials.
Both domains use their actual typed POO configuration/Contract, strict Cedar
schema, current facts and the shared release-bound Gateway admission. Host
predicates below describe a deterministic simulator; no IO is authenticated.
-/
namespace CedarPooSpec.Production.CurrentUse
open Cedar.Spec Cedar.Data Cedar.Validation
open CedarPooSpec.Vertical

inductive Domain where
  | disclosure | payment
  deriving DecidableEq, BEq, Repr

def Domain.label : Domain → String
  | .disclosure => "health-disclosure"
  | .payment => "financial-payment"

private def uid (kind name : String) : EntityUID := ⟨⟨kind, []⟩, name⟩
private def actor := uid "User" "operator"
private def controller := uid "Role" "controller"
private def senior := uid "Role" "senior"
private def target := uid "Resource" "destination"
private def action := uid "Action" "release"

def disclosureTemplate : Health.DisclosureChannel :=
  { policyId := "disclosure", action, destination := target,
    purpose := "treatment", payloadClass := "minimum" }

def paymentTemplate : FinancialServices.ControllerRelease :=
  { policyId := "controller", action, controllerGroup := controller,
    seniorGroup := senior, resourceScope := .resourceScope (.eq target), threshold := "500.0000" }

/-- Contract-checked projection; no raw policy fallback on profile rejection. -/
def selectedPolicy (domain : Domain) : Except String Policy :=
  match domain with
  | .disclosure =>
    match Health.DisclosureProfile.define "Disclosure" disclosureTemplate with
    | .error _ => .error "disclosure construction rejected"
    | .ok object => match Health.DisclosureProfile.policy? object with
      | some policy => .ok policy
      | none => .error "disclosure Contract rejected"
  | .payment =>
    match FinancialServices.ControllerReleaseProfile.define "Payment" paymentTemplate with
    | .error _ => .error "payment construction rejected"
    | .ok object => match FinancialServices.ControllerReleaseProfile.policy? object with
      | some policy => .ok policy
      | none => .error "payment Contract rejected"

private def emptyData (parents : List EntityUID := []) : EntityData :=
  { attrs := Map.empty, ancestors := Set.make parents, tags := Map.empty }

-- Finite decimal literals still use Cedar's parser, never floating point.
private def amount (within : Bool) : Value :=
  .ext (.decimal ((Cedar.Spec.Ext.Decimal.decimal
    (if within then "250.0000" else "750.0000")).get (by cases within <;> native_decide)))

def entities (domain : Domain) (currentFact : Bool) : Entities :=
  let attrs := if domain == .payment then
    Map.make [("amount", amount currentFact), ("matched", .prim (.bool true))]
    else Map.empty
  Map.make [(actor, emptyData [controller]), (controller, emptyData), (senior, emptyData),
    (target, { attrs, ancestors := Set.empty, tags := Map.empty }), (action, emptyData)]

def request (domain : Domain) (currentFact : Bool) : Request :=
  ⟨actor, action, target, if domain == .disclosure then Map.make [
    ("purpose", .prim (.string "treatment")), ("payloadClass", .prim (.string "minimum")),
    ("patientMatches", .prim (.bool currentFact)), ("delegationActive", .prim (.bool true))]
    else Map.empty⟩

def schema (domain : Domain) : Schema :=
  let empty : EntitySchemaEntry := .standard ⟨Set.empty, Map.empty, none⟩
  let resource : EntitySchemaEntry := .standard ⟨Set.empty,
    if domain == .payment then Map.make [
      ("amount", .required (.ext .decimal)), ("matched", .required (.bool .anyBool))]
    else Map.empty, none⟩
  let context := if domain == .disclosure then Map.make [
    ("purpose", .required .string), ("payloadClass", .required .string),
    ("patientMatches", .required (.bool .anyBool)), ("delegationActive", .required (.bool .anyBool))]
    else Map.empty
  ⟨Map.make [(actor.ty, .standard ⟨Set.make [controller.ty], Map.empty, none⟩),
      (controller.ty, empty), (target.ty, resource)],
    Map.make [(action, ⟨Set.make [actor.ty], Set.make [target.ty], Set.empty, context⟩)]⟩

private def model (policy : Policy) : PolicyModules.Model :=
  { modules := [{ name := "current", edits := [.extend policy] }] }
private def scope (domain : Domain) : Gateway.Scope :=
  { originalRoot := "release", claim := "effect", canonicalOperation := "release/effect",
    profile := domain.label, budgetDomain := "budget", historyDomain := "history",
    schemaIdentity := domain.label, sourceCut := "production-v1", moduleClosure := "current",
    projectionClosure := domain.label }
private def context (domain : Domain) : Gateway.Context := ⟨scope domain, 7, 1, 1, 1⟩
private def profile (domain : Domain) : Gateway.Profile := ⟨domain.label, ["source"]⟩

structure View where
  domain : Domain
  fact : Bool
  release : Authorization.Delta.ReleaseState

private def host : Gateway.ZeroTrust.Host Domain View where
  context := fun view => context view.domain
  operations := fun _ => {}
  authorities := fun _ => {}
  authenticated := fun _ => False
  currentAtUse := fun _ => False
  authoritativeProfile := fun _ _ _ _ => False
  committed := fun _ _ => False
  unknownRetained := fun _ _ => False
  revoked := fun _ => False
  mediated := fun _ _ => False

/-- These vectors test semantic admission only. False Host premises deliberately
prevent their interpretation as an authenticated or committed FinalUse. -/
def assess (domain : Domain) (policy : Policy) (view : View) : Except Gateway.Error Bool := do
  let prepared ← Gateway.prepare (model policy) "current" (schema domain) (context domain)
    (profile domain) request domain view.fact
  let _ ← Gateway.ZeroTrust.authorizeCurrent (profile domain) host (fun _ => prepared)
    (fun _ => model policy) View.fact (fun _ => [⟨"source", .satisfied⟩])
    (fun image => entities domain image.fact) View.release domain view
  return true

/-- The generic proof binds these profiles to actual active policies, not an
industry-specific Boolean authorization implementation. -/
theorem admission_binds_release
    (preparedAt : View → Gateway.Prepared Domain Bool request)
    (modelAt : View → PolicyModules.Model) (view : View)
    (accepted : Gateway.ZeroTrust.currentAdmission (profile view.domain) host preparedAt modelAt
      View.fact (fun _ => [⟨"source", .satisfied⟩])
      (fun image => entities view.domain image.fact) View.release view.domain view) :
    view.release.activeRoot = (preparedAt view).policy.root ∧
    view.release.executionMode = .enforcing ∧
    view.release.epoch = (context view.domain).policyRevision ∧
    Authorization.Delta.errorFreeAllow view.release.activePolicies
      (Env.mk (request view.domain view.fact) (entities view.domain view.fact)) = true :=
  Gateway.ZeroTrust.current_admission_binds_active_release _ _ _ _ _ _ _ _ accepted

private def variants (policy : Policy) : List (String × Authorization.Delta.ReleaseState) :=
  let active : Authorization.Delta.ReleaseState := ⟨"current", [policy], .enforcing, 7⟩
  [("current", active), ("changed-root", {active with activeRoot := "retired"}),
   ("changed-policies", {active with activePolicies := []}),
   ("observing", {active with executionMode := .observing}),
   ("disabled", {active with executionMode := .disabled}),
   ("changed-epoch", {active with epoch := 8})]

/-- Independent SDK replay consumes full Cedar inputs; use rows additionally
carry independently read release inputs and the Lean admission result. -/
def fixture : Except String Lean.Json := do
  let mut cases : List Lean.Json := []
  let mut uses : List Lean.Json := []
  let mut schemas : List (String × Lean.Json) := []
  for domain in [Domain.disclosure, .payment] do
    let policy ← selectedPolicy domain
    schemas := schemas ++ [(domain.label, ← (SchemaJson.schema (schema domain)).mapError reprStr)]
    let program ← (Functional.prepareProgram Functional.cedar (model policy) (schema domain)
      ["current"]).mapError Functional.Error.message
    for fact in [false, true] do
      let name := s!"{domain.label}-{fact}"
      cases := cases ++ [← program.authorizationCase name domain.label "current"
        (request domain fact) (entities domain fact)]
      for (variant, release) in variants policy do
        let activePolicies ← (PolicyJson.policySet release.activePolicies).mapError reprStr
        uses := uses ++ [Lean.Json.mkObj [
          ("case_name", Lean.toJson name), ("variant", Lean.toJson variant),
          ("prepared_root", Lean.toJson "current"), ("prepared_epoch", Lean.toJson (7 : Nat)),
          ("active_root", Lean.toJson release.activeRoot), ("active_epoch", Lean.toJson release.epoch),
          ("mode", Lean.toJson (match release.executionMode with
            | .enforcing => "enforcing" | .observing => "observing" | .disabled => "disabled")),
          ("active_policies", activePolicies),
          ("accepted", Lean.toJson ((assess domain policy ⟨domain, fact, release⟩).isOk))]]
  return Lean.Json.mkObj [("format_version", Lean.toJson (1 : Nat)),
    ("schemas", Lean.Json.mkObj schemas),
    ("manifest", Lean.Json.mkObj [("cases", Lean.toJson cases)]), ("uses", Lean.toJson uses)]

end CedarPooSpec.Production.CurrentUse
