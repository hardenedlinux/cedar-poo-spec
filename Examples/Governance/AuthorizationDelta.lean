import CedarPooSpec.Authorization.Delta.Json
import Examples.Governance.TicketSharing

/-!
The same ticket-sharing C4 graph first narrows access through device posture,
then grants access to another ticket. Cedar SymCC analyzes both revisions over
every request type declared by the example schema.
-/

namespace CedarPooSpec.TicketSharingDelta

open CedarPooSpec.TicketSharingExample
open CedarPooSpec.Authorization.Delta

def run : IO Lean.Json := do
  let narrowed ← match ← analyzeModelImpactExplained model "Published" "Posture" schema with
    | .ok report => pure report
    | .error error => throw (IO.userError s!"posture analysis: {reprStr error}")
  if !narrowed.symbolic.noGain then
    throw (IO.userError "posture revision unexpectedly expands authorization")
  let expanded ← match ← analyzeModelImpactExplained expandedModel "Revoked" "Expanded" schema with
    | .ok report => pure report
    | .error error => throw (IO.userError s!"grant analysis: {reprStr error}")
  if expanded.symbolic.noGain then
    throw (IO.userError "new ticket grant has no expansion witness")
  let narrowReport : Report :=
    { changedPolicyIds := narrowed.symbolic.changedPolicyIds
      environmentsChecked := narrowed.symbolic.environmentsChecked
      expansions := narrowed.symbolic.gains }
  let expandedReport : Report :=
    { changedPolicyIds := expanded.symbolic.changedPolicyIds
      environmentsChecked := expanded.symbolic.environmentsChecked
      expansions := expanded.symbolic.gains }
  let .ok narrowJson := CedarPooSpec.Authorization.Delta.Json.report narrowReport
    | throw (IO.userError "could not render posture report")
  let .ok expandedJson := CedarPooSpec.Authorization.Delta.Json.report expandedReport
    | throw (IO.userError "could not render grant counterexample")
  let .ok narrowImpact := CedarPooSpec.Authorization.Delta.Json.impactReport narrowed.symbolic
    | throw (IO.userError "could not render posture impact")
  let .ok expandedImpact := CedarPooSpec.Authorization.Delta.Json.impactReport expanded.symbolic
    | throw (IO.userError "could not render grant impact")
  let .ok postureManifest := CedarPooSpec.Authorization.Delta.Json.impactWitnessCases
    narrowed.symbolic model "Published" "Posture"
    | throw (IO.userError "could not render Cedar posture witness cases")
  let .ok manifest := CedarPooSpec.Authorization.Delta.Json.impactWitnessCases
    expanded.symbolic expandedModel "Revoked" "Expanded"
    | throw (IO.userError "could not render Cedar witness cases")
  return Lean.Json.mkObj [("posture", narrowJson), ("new_grant", expandedJson),
    ("posture_impact", narrowImpact), ("new_grant_impact", expandedImpact),
    ("posture_explanation", CedarPooSpec.Authorization.Delta.Json.explainedImpactReport narrowed),
    ("new_grant_explanation", CedarPooSpec.Authorization.Delta.Json.explainedImpactReport expanded),
    ("posture_manifest", postureManifest), ("manifest", manifest)]

end CedarPooSpec.TicketSharingDelta

def main : IO Unit := do
  IO.println (← CedarPooSpec.TicketSharingDelta.run).compress
