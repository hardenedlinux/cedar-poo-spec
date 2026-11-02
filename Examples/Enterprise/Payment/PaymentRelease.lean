import CedarPooSpec.Governance.SeparationOfDuties
import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Vertical.FinancialServices.ControllerReleaseProfile

/-!
Two authorization queries form one payment release. The controls illustrate
separation of duties and compound authorization; all amounts and identities
are fictive application assumptions.
-/

namespace CedarPooSpec.PaymentReleaseExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Governance
open CedarPooSpec.Vertical.FinancialServices

def userType : EntityType := ⟨"User", []⟩
def roleType : EntityType := ⟨"Role", []⟩
def paymentType : EntityType := ⟨"Payment", []⟩
def groupType : EntityType := ⟨"PaymentGroup", []⟩
def actionType : EntityType := ⟨"Action", []⟩

def alice : EntityUID := ⟨userType, "alice"⟩
def bob : EntityUID := ⟨userType, "bob"⟩
def carol : EntityUID := ⟨userType, "carol"⟩
def dave : EntityUID := ⟨userType, "dave"⟩
def clerk : EntityUID := ⟨roleType, "Clerk"⟩
def controller : EntityUID := ⟨roleType, "Controller"⟩
def senior : EntityUID := ⟨roleType, "SeniorController"⟩
def operations : EntityUID := ⟨groupType, "Operations"⟩
def research : EntityUID := ⟨groupType, "Research"⟩
def small : EntityUID := ⟨paymentType, "small"⟩
def large : EntityUID := ⟨paymentType, "large"⟩
def frozen : EntityUID := ⟨paymentType, "frozen"⟩
def unmatched : EntityUID := ⟨paymentType, "unmatched"⟩
def researchPayment : EntityUID := ⟨paymentType, "research"⟩
def sameActor : EntityUID := ⟨paymentType, "same-actor"⟩
def prepare : EntityUID := ⟨actionType, "prepare"⟩
def release : EntityUID := ⟨actionType, "release"⟩

def decimal (text : String) : Cedar.Spec.Ext.Decimal :=
  match Cedar.Spec.Ext.Decimal.decimal text with
  | some value => value
  | none => panic! s!"invalid payment amount: {text}"

def emptyData (parents : List EntityUID := []) : EntityData :=
  { attrs := Map.empty, ancestors := Set.make parents, tags := Map.empty }

def paymentData (owner group : EntityUID) (amount : String)
    (matched blocked : Bool) : EntityData :=
  { attrs := Map.make [
      ("preparedBy", .prim (.entityUID owner)),
      ("amount", .ext (.decimal (decimal amount))),
      ("matched", .prim (.bool matched)),
      ("blocked", .prim (.bool blocked))],
    ancestors := Set.make [group], tags := Map.empty }

def entities : Entities := Map.make [
  (alice, emptyData [clerk]), (bob, emptyData [controller]),
  (carol, emptyData [controller, senior]),
  (dave, emptyData [clerk, controller]),
  (clerk, emptyData), (controller, emptyData), (senior, emptyData),
  (operations, emptyData), (research, emptyData),
  (small, paymentData alice operations "250.0000" true false),
  (large, paymentData alice operations "750.0000" true false),
  (frozen, paymentData alice operations "250.0000" true true),
  (unmatched, paymentData alice operations "250.0000" false false),
  (researchPayment, paymentData alice research "250.0000" true false),
  (sameActor, paymentData dave operations "250.0000" true false),
  (prepare, emptyData), (release, emptyData)]

def userEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [roleType], Map.empty, none⟩
def roleEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.empty, none⟩
def paymentEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [groupType], Map.make [
    ("preparedBy", .required (.entity userType)),
    ("amount", .required (.ext .decimal)),
    ("matched", .required (.bool .anyBool)),
    ("blocked", .required (.bool .anyBool))], none⟩
def groupEntry : EntitySchemaEntry :=
  .standard ⟨Set.empty, Map.empty, none⟩
def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [userType], Set.make [paymentType], Set.empty, Map.empty⟩
def schema : Schema :=
  ⟨Map.make [(userType, userEntry), (roleType, roleEntry),
    (paymentType, paymentEntry), (groupType, groupEntry)],
    Map.make [(prepare, actionEntry), (release, actionEntry)]⟩

def paymentFact (name : String) : Expr := .getAttr (.var .resource) name

def positive : Expr :=
  .call .greaterThan [paymentFact "amount", .call .decimal [.lit (.string "0.0000")]]
def matched : Expr := paymentFact "matched"
def blocked : Expr := paymentFact "blocked"
def selfRelease : Expr :=
  .binaryApp .eq (.var .principal) (paymentFact "preparedBy")
def policy (id : String) (effect : Effect) (action : EntityUID)
    (scope : Scope) (body : Expr) : Policy :=
  { id, effect,
    principalScope := .principalScope scope,
    actionScope := .actionScope (.eq action),
    resourceScope := .resourceScope (.mem operations),
    condition := [{ kind := .when, body }] }

def preparePermit : Policy :=
  policy "prepare-matched-payment" .permit prepare (.mem clerk)
    (.and selfRelease (.and matched positive))
def controllerTemplate : ControllerRelease :=
  { policyId := "controller-release", action := release,
    controllerGroup := controller, seniorGroup := senior,
    resourceScope := .resourceScope (.mem operations), threshold := "500.0000" }
def controllerProfile : ControllerReleaseProfile.Object :=
  (ControllerReleaseProfile.define "ControllerRelease" controllerTemplate).toOption.get
    (by native_decide)

/-- One admission for all projections of this exact immutable profile. -/
def controllerProfileAccess : CedarPooSpec.Functional.ObjectProfile.Session ControllerReleaseProfile.contract (CedarPooSpec.Functional.ObjectProfile.factory ControllerReleaseProfile.contract) controllerProfile :=
  (CedarPooSpec.Functional.ObjectProfile.Session.open ControllerReleaseProfile.contract
    (CedarPooSpec.Functional.ObjectProfile.factory ControllerReleaseProfile.contract) controllerProfile).toOption.get (by native_decide)

def controllerRelease : ControllerRelease :=
  (controllerProfileAccess.read .control).get (by native_decide)

def controllerPolicy : Policy :=
  (controllerProfileAccess.read .policy).get (by native_decide)

def restrictedControllerProfile : ControllerReleaseProfile.Object :=
  (ControllerReleaseProfile.withThreshold controllerProfile "RestrictedControllerRelease"
    "200.0000").toOption.get (by native_decide)

def restrictedControllerPolicy : Policy :=
  (ControllerReleaseProfile.policy? restrictedControllerProfile).get (by native_decide)
def legacyBypass : Policy :=
  policy "legacy-matched-release" .permit release .any matched

def dutiesControl : SeparationOfDuties :=
  { policyId := "separate-preparer-and-releaser",
    actionScope := .actionScope (.eq release),
    priorActorAttribute := "preparedBy",
    resourceScope := .resourceScope (.mem operations) }
def dutiesVeto : Policy := dutiesControl.veto.policy

def riskVeto : Policy :=
  policy "block-frozen-payment" .forbid release .any blocked

def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits := [.extend preparePermit, controllerRelease.introduce,
        .extend legacyBypass] }] }
  let threshold ← base.extend "Threshold" "Base" [.overlay controllerPolicy]
  let duties ← threshold.extend "Duties" "Base" [dutiesControl.edit .introduce]
  let risk ← duties.extend "Risk" "Base" [.extend riskVeto]
  let retired ← risk.extend "Retired" "Base" [.remove legacyBypass.id]
  let integrated ← retired.mix "Integrated" ["Threshold", "Duties", "Risk", "Retired"]
  integrated.extend "Restricted" "Integrated" [.overlay restrictedControllerPolicy]

def model : Model := modelResult.toOption.get (by native_decide)

def roots : List String :=
  ["Base", "Threshold", "Duties", "Risk", "Retired", "Integrated", "Restricted"]

def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard model schema roots
      (by native_decide)

def request (principal action resource : EntityUID) : Request :=
  ⟨principal, action, resource, Map.empty⟩

def authorized
     (root : String) (principal action resource : EntityUID)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PaymentReleaseExample.model CedarPooSpec.PaymentReleaseExample.schema :=
      CedarPooSpec.PaymentReleaseExample.program) : Bool :=
  match programContext.authorize root [request principal action resource] entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

/-- The application must require both permissions on the same payment snapshot. -/
def releaseOperation
     (root : String) (preparer releaser resource : EntityUID)
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PaymentReleaseExample.model CedarPooSpec.PaymentReleaseExample.schema :=
      CedarPooSpec.PaymentReleaseExample.program) : Bool :=
  let requests := [request preparer prepare resource, request releaser release resource]
  match programContext.authorize root requests entities with
  | .error _ => false
  | .ok receipt => receipt.allowed

def operationCases : List (String × String × EntityUID × EntityUID × EntityUID × Bool) := [
  ("base-same-actor", "Base", dave, dave, sameActor, true),
  ("integrated-small", "Integrated", alice, bob, small, true),
  ("integrated-wrong-preparer", "Integrated", dave, bob, small, false),
  ("integrated-same-actor", "Integrated", dave, dave, sameActor, false),
  ("integrated-high-controller", "Integrated", alice, bob, large, false),
  ("integrated-high-senior", "Integrated", alice, carol, large, true),
  ("integrated-frozen", "Integrated", alice, bob, frozen, false),
  ("integrated-unmatched", "Integrated", alice, bob, unmatched, false),
  ("integrated-cross-group", "Integrated", alice, bob, researchPayment, false),
  ("integrated-clerk-release", "Integrated", alice, alice, small, false)]

def branchCases : List (String × String × EntityUID × EntityUID × EntityUID × Decision) := [
  ("base-same-actor-release-probe", "Base", dave, release, sameActor, .allow),
  ("duties-same-actor-release", "Duties", dave, release, sameActor, .deny),
  ("threshold-high-release", "Threshold", bob, release, large, .allow),
  ("retired-high-release", "Retired", bob, release, large, .allow),
  ("integrated-high-release", "Integrated", bob, release, large, .deny),
  ("base-frozen-release", "Base", bob, release, frozen, .allow),
  ("risk-frozen-release", "Risk", bob, release, frozen, .deny),
  ("integrated-unmatched-release-probe", "Integrated", bob, release, unmatched, .deny)]

def operationsExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PaymentReleaseExample.model CedarPooSpec.PaymentReleaseExample.schema :=
      CedarPooSpec.PaymentReleaseExample.program) : Bool := operationCases.all fun (_, root, preparer, releaser, resource, expected) =>
  (releaseOperation (programContext := programContext)) root preparer releaser resource == expected

theorem operationsExactFully : operationsExact = true := by native_decide

theorem emptyCompoundRejected :
    (match program.authorize "Integrated" [] entities with
     | .ok receipt => receipt.allowed
     | .error _ => false) = false := by native_decide

def branchCasesExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PaymentReleaseExample.model CedarPooSpec.PaymentReleaseExample.schema :=
      CedarPooSpec.PaymentReleaseExample.program) : Bool := branchCases.all fun (_, root, principal, action, resource, expected) =>
  match programContext.response root (request principal action resource) entities with
  | .error _ => false
  | .ok response =>
      response.decision == expected && response.erroringPolicies.isEmpty

theorem branchCasesExactFully : branchCasesExact = true := by native_decide

def controlsNeedComposition
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PaymentReleaseExample.model CedarPooSpec.PaymentReleaseExample.schema :=
      CedarPooSpec.PaymentReleaseExample.program) : Bool :=
  (releaseOperation (programContext := programContext)) "Base" dave dave sameActor &&
  !(releaseOperation (programContext := programContext)) "Duties" dave dave sameActor &&
  (releaseOperation (programContext := programContext)) "Threshold" alice bob large &&
  (releaseOperation (programContext := programContext)) "Retired" alice bob large &&
  !(releaseOperation (programContext := programContext)) "Integrated" alice bob large &&
  (releaseOperation (programContext := programContext)) "Base" alice bob frozen &&
  !(releaseOperation (programContext := programContext)) "Risk" alice bob frozen &&
  !(authorized (programContext := programContext)) "Integrated" bob release unmatched

theorem controlsNeedCompositionFully : controlsNeedComposition = true := by
  native_decide

theorem thresholdEditLocal :
    ((model.compileRevision "Base" "Threshold").toOption.get
      (by native_decide)).changedPolicyIds = ["controller-release"] := by native_decide

def integratedPolicyIdsExact : Bool :=
  let ids := ((model.compile "Integrated").toOption.get (by native_decide)).map Policy.id
  ids.length == 4 &&
  ["prepare-matched-payment", "controller-release",
   "separate-preparer-and-releaser", "block-frozen-payment"].all ids.contains &&
  !ids.contains "legacy-matched-release"

theorem legacyRetired : integratedPolicyIdsExact = true := by native_decide

theorem validatedIntegrated :
    (program.publish "Integrated").isOk = true := by
  native_decide

def allRootsValidated
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.PaymentReleaseExample.model CedarPooSpec.PaymentReleaseExample.schema :=
      CedarPooSpec.PaymentReleaseExample.program) : Bool :=
  roots.all fun root => (programContext.publish root).isOk

theorem allRootsValidatedFully : allRootsValidated = true := by native_decide

end CedarPooSpec.PaymentReleaseExample
