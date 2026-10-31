import CedarPooSpec.Authorization.Delta.Json
import Examples.Health.Pseudonymization

/-!
Analyze an application-owned incident overlay and its removal. No cloud
provider participates in policy composition or Cedar's symbolic query.
-/

namespace CedarPooSpec.PseudonymizationExample.AuthorizationImpact

open CedarPooSpec.Authorization.Delta
open CedarPooSpec.PseudonymizationExample
open Cedar.Spec Cedar.Data

private def replaceDataset (uid : EntityUID) (data : EntityData) : Entities :=
  Map.make ((uid, data) :: entities.toList.filter (fun entry => entry.1 != uid))

def run : IO Lean.Json := do
  let .ok policies := model.compile hospitalView.name
    | throw (IO.userError "could not compile hospital policy root")
  let beforeSnapshot : Cedar.Spec.Env :=
    ⟨request agent PseudonymizationExample.join hospital {}, entities⟩
  let afterSnapshot : Cedar.Spec.Env :=
    ⟨request agent PseudonymizationExample.join hospital { joinApproved := false }, entities⟩
  let .ok approvalImpact := compareOperationSnapshots schema policies policies
    beforeSnapshot afterSnapshot
    | throw (IO.userError "could not compare approval snapshots")
  if !approvalImpact.lost || approvalImpact.gained then
    throw (IO.userError "approval withdrawal must revoke the selected join")
  let switchedTarget : Cedar.Spec.Env :=
    ⟨request agent PseudonymizationExample.join research { joinApproved := false }, entities⟩
  match compareOperationSnapshots schema policies policies beforeSnapshot switchedTarget with
  | .error .operationChanged => pure ()
  | _ => throw (IO.userError "different dataset cannot be reported as one operation delta")
  let linkedRequest := request agent PseudonymizationExample.join hospital
    { targetDataset := rewrapped }
  let linkedBefore : Cedar.Spec.Env := ⟨linkedRequest, entities⟩
  let lineageChanges ← [
    ("scope", datasetData .aesSiv "study-two"),
    ("token-key", datasetData .aesSiv "hospital-a"
      { hospitalLineage with tokenKeyVersion := "dek-v2" }),
    ("transform", datasetData .aesSiv "hospital-a"
      { hospitalLineage with transformVersion := "patient-id-v2" })
  ].mapM fun (kind, replacement) => do
    let after : Cedar.Spec.Env :=
      ⟨linkedRequest, replaceDataset rewrapped replacement⟩
    let .ok impact := compareOperationSnapshots schema policies policies linkedBefore after
      | throw (IO.userError s!"could not compare {kind} snapshots")
    if !impact.lost || impact.gained then
      throw (IO.userError s!"{kind} change did not revoke the selected join")
    let .ok report := CedarPooSpec.Authorization.Delta.Json.snapshotReport
      impact linkedBefore after
      | throw (IO.userError s!"could not render {kind} snapshots")
    let .ok manifest := CedarPooSpec.Authorization.Delta.Json.snapshotCases
      kind model hospitalView.name hospitalView.name linkedBefore after
      | throw (IO.userError s!"could not render {kind} replay cases")
    pure <| Lean.Json.mkObj [
      ("kind", Lean.toJson kind), ("report", report), ("manifest", manifest)]
  let suspended ← match ← analyzeModelImpact model hospitalView.name incident.name schema with
    | .ok report => pure report
    | .error error => throw (IO.userError s!"suspension analysis: {reprStr error}")
  if !suspended.noGain || suspended.noLoss then
    throw (IO.userError "incident must revoke access without granting access")
  let restored ← match ← analyzeModelImpact model incident.name recovered.name schema with
    | .ok report => pure report
    | .error error => throw (IO.userError s!"recovery analysis: {reprStr error}")
  if restored.noGain || !restored.noLoss then
    throw (IO.userError "recovery must restore access without revoking access")
  let .ok suspendedJson := CedarPooSpec.Authorization.Delta.Json.impactReport suspended
    | throw (IO.userError "could not render incident impact")
  let .ok restoredJson := CedarPooSpec.Authorization.Delta.Json.impactReport restored
    | throw (IO.userError "could not render recovery impact")
  let .ok suspendedManifest := CedarPooSpec.Authorization.Delta.Json.impactWitnessCases
    suspended model hospitalView.name incident.name
    | throw (IO.userError "could not render incident witnesses")
  let .ok restoredManifest := CedarPooSpec.Authorization.Delta.Json.impactWitnessCases
    restored model incident.name recovered.name
    | throw (IO.userError "could not render recovery witnesses")
  let .ok approvalJson := CedarPooSpec.Authorization.Delta.Json.snapshotReport
    approvalImpact beforeSnapshot afterSnapshot
    | throw (IO.userError "could not render approval snapshots")
  let .ok approvalManifest := CedarPooSpec.Authorization.Delta.Json.snapshotCases
    "approval" model hospitalView.name hospitalView.name beforeSnapshot afterSnapshot
    | throw (IO.userError "could not render approval replay cases")
  return Lean.Json.mkObj [
    ("suspended", suspendedJson), ("restored", restoredJson),
    ("suspended_manifest", suspendedManifest),
    ("restored_manifest", restoredManifest),
    ("approval_withdrawal", approvalJson),
    ("approval_manifest", approvalManifest),
    ("lineage_changes", Lean.toJson lineageChanges)]

end CedarPooSpec.PseudonymizationExample.AuthorizationImpact

def main : IO Unit := do
  IO.println (← CedarPooSpec.PseudonymizationExample.AuthorizationImpact.run).compress
