import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.Governance.MemberGrant
import CedarPooSpec.Governance.Veto

/-!
Resource-specific approver roles follow Cedar's documented country timesheet
pattern. The broad legacy grant and classification veto are explicit local
revision assumptions, with fictive identities and records.
-/

namespace CedarPooSpec.CountryApprovalExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules
open CedarPooSpec.Governance

def userType : EntityType := ⟨"User", []⟩
def roleType : EntityType := ⟨"Role", []⟩
def sheetType : EntityType := ⟨"Timesheet", []⟩
def groupType : EntityType := ⟨"TimesheetGrp", []⟩
def actionType : EntityType := ⟨"Action", []⟩

def alice : EntityUID := ⟨userType, "alice"⟩
def bob : EntityUID := ⟨userType, "bob"⟩
def charlie : EntityUID := ⟨userType, "charlie"⟩
def france : EntityUID := ⟨roleType, "Approver-France"⟩
def germany : EntityUID := ⟨roleType, "Approver-Germany"⟩
def uk : EntityUID := ⟨roleType, "Approver-UK"⟩
def japan : EntityUID := ⟨roleType, "Approver-Japan"⟩
def europe : EntityUID := ⟨roleType, "Approver-Europe"⟩
def frenchTeam : EntityUID := ⟨roleType, "French-Team"⟩
def frenchSheets : EntityUID := ⟨groupType, "French-timesheets"⟩
def germanSheets : EntityUID := ⟨groupType, "German-timesheets"⟩
def ukSheets : EntityUID := ⟨groupType, "UK-timesheets"⟩
def japaneseSheets : EntityUID := ⟨groupType, "Japanese-timesheets"⟩
def europeanSheets : EntityUID := ⟨groupType, "European-timesheets"⟩
def parisSheets : EntityUID := ⟨groupType, "Paris-timesheets"⟩
def frenchSheet : EntityUID := ⟨sheetType, "fr-1"⟩
def germanSheet : EntityUID := ⟨sheetType, "de-1"⟩
def ukSheet : EntityUID := ⟨sheetType, "uk-1"⟩
def japaneseSheet : EntityUID := ⟨sheetType, "jp-1"⟩
def restrictedSheet : EntityUID := ⟨sheetType, "fr-restricted"⟩
def approve : EntityUID := ⟨actionType, "approve"⟩
def review : EntityUID := ⟨actionType, "review"⟩
def delete : EntityUID := ⟨actionType, "delete"⟩
def approverActions : EntityUID := ⟨actionType, "ApproverActions"⟩

def userEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [roleType], Map.empty, some .string⟩
def roleEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [roleType], Map.empty, none⟩
def sheetEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [groupType], Map.empty, some .string⟩
def groupEntry : EntitySchemaEntry :=
  .standard ⟨Set.make [groupType], Map.empty, none⟩
def actionEntry (ancestors : Set EntityUID := Set.empty) : ActionSchemaEntry :=
  ⟨Set.make [userType], Set.make [sheetType], ancestors, Map.empty⟩
def schema : Schema :=
  ⟨Map.make [(userType, userEntry), (roleType, roleEntry),
      (sheetType, sheetEntry), (groupType, groupEntry)],
    Map.make [(approve, actionEntry (Set.make [approverActions])),
      (review, actionEntry (Set.make [approverActions])),
      (delete, actionEntry), (approverActions, actionEntry)]⟩

def data (parents : List EntityUID := []) (tags : List (String × Value) := []) :
    EntityData :=
  { attrs := Map.empty, ancestors := Set.make parents, tags := Map.make tags }

/-- One jurisdiction owns its role, resource group, ancestry, and policy ID.
    Adding a jurisdiction appends one value rather than parallel declarations. -/
structure ApprovalObject where
  policyId : String
  approverRole : EntityUID
  roleParents : List EntityUID
  sheetGroup : EntityUID
  groupParents : List EntityUID

def baseApprovals : List ApprovalObject := [
  ⟨"france", france, [europe], frenchSheets, [europeanSheets]⟩,
  ⟨"germany", germany, [europe], germanSheets, [europeanSheets]⟩]
def expandedApprovals : List ApprovalObject := [
  ⟨"uk", uk, [europe], ukSheets, [europeanSheets]⟩,
  ⟨"japan", japan, [], japaneseSheets, []⟩]
def approvals : List ApprovalObject := baseApprovals ++ expandedApprovals

def ApprovalObject.entities (object : ApprovalObject) : List (EntityUID × EntityData) := [
  (object.approverRole, data object.roleParents),
  (object.sheetGroup, data object.groupParents)]

def entities : Entities := Map.make ([
  (alice, data [frenchTeam, france, europe] [("clearance", .prim (.string "restricted"))]),
  (bob, data [germany, uk, japan, europe]),
  (charlie, data [france, europe]),
  (frenchTeam, data [france, europe]),
  (europe, data), (europeanSheets, data)] ++
  approvals.flatMap ApprovalObject.entities ++ [
  (parisSheets, data [frenchSheets, europeanSheets]),
  (frenchSheet, data [parisSheets, frenchSheets, europeanSheets]),
  (restrictedSheet, data [parisSheets, frenchSheets, europeanSheets]
    [("classification", .prim (.string "restricted"))]),
  (germanSheet, data [germanSheets, europeanSheets]),
  (ukSheet, data [ukSheets, europeanSheets]),
  (japaneseSheet, data [japaneseSheets]),
  (approve, data [approverActions]), (review, data [approverActions]),
  (delete, data), (approverActions, data)])

def ApprovalObject.grant (object : ApprovalObject) : MemberGrant :=
  { policyId := object.policyId, principalGroup := object.approverRole,
    actionScope := .actionScope (.mem approverActions),
    resourceGroup := object.sheetGroup }

-- This legacy grant is intentionally too broad; the integrated root removes it.
def legacyEurope : MemberGrant :=
  { policyId := "legacy-europe", principalGroup := europe,
    actionScope := .actionInAny [approve, review],
    resourceGroup := europeanSheets }

def tag (subject : Expr) (key : String) : Expr :=
  .binaryApp .getTag subject (.lit (.string key))
def hasTag (subject : Expr) (key : String) : Expr :=
  .binaryApp .hasTag subject (.lit (.string key))
def sensitiveCondition : Expr :=
  .and (hasTag (.var .resource) "classification")
    (.unaryApp .not (.and (hasTag (.var .principal) "clearance")
      (.binaryApp .eq (tag (.var .principal) "clearance")
        (tag (.var .resource) "classification"))))
def sensitiveControl : Veto :=
  { policyId := "restricted-clearance",
    actionScope := .actionScope (.mem approverActions),
    denyWhen := sensitiveCondition,
    resourceScope := .resourceScope (.is sheetType) }
def modelResult : Except LeanPoo.C4.Error Model := do
  let base : Model := { modules := [
    { name := "Base", edits :=
        baseApprovals.map (fun object => object.grant.edit .introduce) ++
          [legacyEurope.edit .introduce] }] }
  let expansion ← base.extend "Expansion" "Base"
    (expandedApprovals.map (fun object => object.grant.edit .introduce))
  let sensitive ← expansion.extend "Sensitive" "Base"
    [sensitiveControl.edit .introduce]
  sensitive.mix "Integrated" ["Expansion", "Sensitive"]
    [legacyEurope.edit .withdraw]

def model : Model := modelResult.toOption.get (by native_decide)

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)


theorem approvalObjectsPopulateEntities :
    approvals.all (fun object =>
      entities.contains object.approverRole &&
      entities.contains object.sheetGroup) = true := by native_decide

theorem approvalObjectsPopulatePolicies :
    approvals.all (fun object =>
      ((model.compile "Integrated").toOption.get (by native_decide)).any
        (fun policy => policy.id == object.policyId)) = true := by native_decide

def schemaValidationExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.CountryApprovalExample.model CedarPooSpec.CountryApprovalExample.schema :=
      CedarPooSpec.CountryApprovalExample.program) : Bool :=
  ["Base", "Expansion", "Sensitive", "Integrated"].all fun root => (programContext.at root).isOk

theorem schemaValidationFully : schemaValidationExact = true := by native_decide

def request (principal action resource : EntityUID) : Request :=
  ⟨principal, action, resource, Map.empty⟩

def cases : List (String × String × Request × Decision) := [
  ("legacy-cross-country", "Base", request alice approve germanSheet, .allow),
  ("sensitive-cross-country", "Sensitive", request alice approve germanSheet, .allow),
  ("integrated-cross-country", "Integrated", request alice approve germanSheet, .deny),
  ("france-nested-role", "Integrated", request alice approve frenchSheet, .allow),
  ("france-review-action", "Integrated", request alice review frenchSheet, .allow),
  ("france-unrelated-action", "Integrated", request alice delete frenchSheet, .deny),
  ("germany-role", "Integrated", request bob approve germanSheet, .allow),
  ("uk-expansion", "Integrated", request bob approve ukSheet, .allow),
  ("japan-expansion", "Integrated", request bob approve japaneseSheet, .allow),
  ("japan-cross-country", "Integrated", request alice approve japaneseSheet, .deny),
  ("restricted-cleared", "Integrated", request alice approve restrictedSheet, .allow),
  ("restricted-before-veto", "Expansion", request charlie approve restrictedSheet, .allow),
  ("restricted-after-veto", "Integrated", request charlie approve restrictedSheet, .deny)]

def decisionsExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.CountryApprovalExample.model CedarPooSpec.CountryApprovalExample.schema :=
      CedarPooSpec.CountryApprovalExample.program) : Bool := cases.all fun (_, root, req, expected) =>
  match programContext.response root req entities with
  | .error _ => false
  | .ok response =>
      response.decision == expected && response.erroringPolicies.isEmpty

theorem decisionsExactFully : decisionsExact = true := by native_decide

theorem expansionEditLocal :
    ((model.compileRevision "Base" "Expansion").toOption.get
      (by native_decide)).changedPolicyIds = ["uk", "japan"] := by native_decide
theorem sensitiveEditLocal :
    ((model.compileRevision "Base" "Sensitive").toOption.get
      (by native_decide)).changedPolicyIds = ["restricted-clearance"] := by native_decide
theorem integratedEditLocal :
    ((model.compileRevision "Expansion" "Integrated").toOption.get
      (by native_decide)).changedPolicyIds = ["legacy-europe", "restricted-clearance"] := by
  native_decide

def originalCountriesPreserved : Bool :=
  let before := (model.compile "Base").toOption.getD []
  let after := (model.compile "Integrated").toOption.getD []
  ["france", "germany"].all fun id =>
    before.find? (fun policy => policy.id == id) ==
      after.find? (fun policy => policy.id == id)
theorem originalCountriesPreservedFully : originalCountriesPreserved = true := by
  native_decide

theorem integratedRemovesBroadGrant :
    ((model.compile "Integrated").toOption.getD []).map Policy.id =
      ["france", "germany", "restricted-clearance", "uk", "japan"] := by native_decide

def incompleteEntities : Entities := Map.make [
  (alice, data [frenchTeam]),
  (frenchTeam, data [france]),
  (france, data)]

theorem incompleteHierarchyRejected :
    (match CedarPooSpec.PolicyJson.entities incompleteEntities with
     | .error (.incompleteEntityAncestors _) => true
     | _ => false) = true := by native_decide

end CedarPooSpec.CountryApprovalExample
