import CedarPooSpec.PolicyModules

/-! Independent controls for retained source identity, C4 plans and Cedar edits.
The workflows follow LeanPoo's ObjectDefinition and LiveRevision examples. -/
namespace CedarPooSpec.LeanPooAlignmentTest

open Cedar.Spec CedarPooSpec.PolicyModules

def permit : Policy := { Policy.allowAll with id := "owned" }
def forbid : Policy := { permit with effect := .forbid }

def warm : Model :=
  (Model.define "Root" [.extend permit]).toOption.getD { modules := [] }

def revised : Model :=
  { warm with modules := [{ name := "Root", edits := [.extend forbid] }] }

-- A direct source edit invalidates both the object and its old declaration plan.
example : warm.currentObject?.isSome = true := by native_decide
example : revised.currentObject?.isNone = true := by native_decide
example : (revised.compile "Root").toOption = some [forbid] := by native_decide
example : (warm.compile "Root").toOption = some [permit] := by native_decide
example : ((revised.objectAt "Root").toOption.bind (·.read "owned")) =
    some (some forbid) := by native_decide
example : ((revised.explainResolution "Root" "owned").toOption.map (·.precedence)) =
    some ["Root"] := by native_decide

-- Extending an older root uses the staged schema path, not the last object.
def staged : Model :=
  (do
    let first ← warm.extend "First" "Root" [.overlay forbid]
    first.extend "Second" "Root").toOption.getD { modules := [] }

example : staged.currentObject?.isNone = true := by native_decide
example : (staged.compile "First").toOption = some [forbid] := by native_decide
example : (staged.compile "Second").toOption = some [permit] := by native_decide

def staleSchema : Model :=
  { staged with modules := [{ name := "Root", edits := [.extend forbid] }] }

example : (staleSchema.compile "Root").toOption = some [forbid] := by native_decide
example : (staleSchema.compile "Second").isOk = false := by native_decide
example : (staleSchema.explainResolution "Second" "owned").isOk = false := by
  native_decide

-- Tombstone diagnostics use the same plan while final Cedar materialization
-- removes the policy. Merely obtaining a first-class object is not admission.
def removed : Model :=
  (warm.extend "Removed" "Root" [.remove permit.id]).toOption.getD { modules := [] }

example : (removed.compile "Removed").toOption = some [] := by native_decide
example : ((removed.explainResolution "Removed" permit.id).toOption.map (·.precedence)) =
    some ["Removed", "Root"] := by native_decide

def invalid : Model :=
  (Model.define "Invalid" [.overlay forbid]).toOption.getD { modules := [] }

example : (invalid.objectAt "Invalid").isOk = true := by native_decide
example : (invalid.explainResolution "Invalid" permit.id).isOk = true := by native_decide
def missingPolicyRefused : Bool :=
  match invalid.compile "Invalid" with
  | .error (.missingPolicy id) => id == permit.id
  | _ => false

example : missingPolicyRefused = true := by native_decide

end CedarPooSpec.LeanPooAlignmentTest
