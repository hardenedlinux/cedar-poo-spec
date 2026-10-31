import CedarPooSpec.Authorization.Delta.Evidence
import Examples.Governance.TicketSharing
import Tests.Governance.AuthorizationDeltaReasonModels

/-!
Sibling roots can each edit the same Cedar policy ID. Both editor branches
must contribute descendants to the potential C4 invalidation set.
-/

namespace CedarPooSpec.AuthorizationDeltaInvalidationTest

open Cedar.Spec CedarPooSpec.PolicyModules CedarPooSpec.Authorization.Delta
open CedarPooSpec.TicketSharingExample

def sourcePolicy : Policy :=
  (publishedPolicies.find? (·.id == "alice-ticket-a")).get (by native_decide)

def beforePolicy : Policy := { sourcePolicy with effect := .forbid }

def afterPolicy : Policy :=
  { sourcePolicy with
    condition := [{ kind := .when, body := .lit (.bool false) }] }

def siblingModel : Model :=
  let shared := (({ modules := [] } : Model).mix "Shared" []
    [.extend sourcePolicy]).toOption.get (by native_decide)
  let before := (shared.extend "BeforeEditor" "Shared"
    [.overlay beforePolicy]).toOption.get (by native_decide)
  let both := (before.extend "AfterEditor" "Shared"
    [.overlay afterPolicy]).toOption.get (by native_decide)
  let beforeDescendant := (both.extend "BeforeDescendant" "BeforeEditor" [])
    |>.toOption.get (by native_decide)
  (beforeDescendant.extend "AfterDescendant" "AfterEditor" [])
    |>.toOption.get (by native_decide)

def siblingRevision : Revision :=
  (siblingModel.compileRevision "BeforeEditor" "AfterEditor").toOption.get
    (by native_decide)

def siblingChanges : List PolicyChange :=
  CedarPooSpec.Authorization.Delta.Revision.policyChanges siblingRevision

theorem siblingLastEditors :
    siblingChanges.length = 1 ∧
    (siblingChanges.head?.bind fun change =>
      change.beforeEdits.getLast?.map (·.moduleName)) = some "BeforeEditor" ∧
    (siblingChanges.head?.bind fun change =>
      change.afterEdits.getLast?.map (·.moduleName)) = some "AfterEditor" := by
  native_decide

theorem bothBranchesInvalidated :
    let roots := affectedRoots siblingModel siblingChanges
    roots.length = 4 ∧
    roots.contains "BeforeEditor" ∧
    roots.contains "BeforeDescendant" ∧
    roots.contains "AfterEditor" ∧
    roots.contains "AfterDescendant" ∧
    !roots.contains "Shared" := by
  native_decide

/-- Removal is covered even though the after compilation has no policy owner. -/
theorem removalInvalidatesBothSides :
    let revision := (CedarPooSpec.AuthorizationDeltaReasonModels.sharedModel.compileRevision
      "Shared" "OneGrantRemoved").toOption.get (by native_decide)
    let roots := affectedRoots CedarPooSpec.AuthorizationDeltaReasonModels.sharedModel
      (CedarPooSpec.Authorization.Delta.Revision.policyChanges revision)
    roots.contains "Shared" && roots.contains "OneGrantRemoved" := by
  native_decide

/-- A same-body owner transfer has no policy-body delta, but a provenance
    change still produces an invalidation set when passed to affectedRoots. -/
theorem provenanceTransferInvalidatesBothSides :
    let revision := (CedarPooSpec.AuthorizationDeltaReasonModels.ownerModel.compileRevision
      "Shared" "OwnershipShift").toOption.get (by native_decide)
    let changes := CedarPooSpec.Authorization.Delta.Revision.provenanceChanges revision
    let roots := affectedRoots CedarPooSpec.AuthorizationDeltaReasonModels.ownerModel changes
    changes.length = 1 ∧ roots.contains "Shared" ∧
      roots.contains "OwnershipShift" := by
  native_decide

end CedarPooSpec.AuthorizationDeltaInvalidationTest
