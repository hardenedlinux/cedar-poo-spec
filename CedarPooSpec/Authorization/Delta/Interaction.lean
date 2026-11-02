import CedarPooSpec.Functional.Compilation
import CedarPooSpec.Authorization.Delta.Evidence

/-!
Analyze a four-root POO composition. Cedar checks each complete policy set;
the POO graph supplies branch and composition provenance. A joint-only gain is
reported only after both independent branches have no gain over the base.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec CedarPooSpec.PolicyModules

inductive InteractionError where
  | delta (error : Error)
  | compilation (error : PolicyModules.Error)
  | topology (message : String)
  | branchReplayAllowed (root : String) (witness : Cedar.Spec.Env)
  deriving Repr

/-- A concrete gain of the composed root that each branch still denies. -/
structure JointOnlyGain where
  combined : Expansion
  leftResponse : Response
  rightResponse : Response

/-- Branch gains prevent a universal joint-only classification. -/
inductive InteractionOutcome where
  | branchExpanded
  | noCombinedGain
  | jointOnlyGain (witnesses : List JointOnlyGain)

structure InteractionReport where
  baseRoot : String
  left : ExplainedReport
  right : ExplainedReport
  combined : ExplainedReport
  outcome : InteractionOutcome

/-- Compare both branches and their C4 composition against one base under the
    same Cedar schema. The joint-only claim requires empty symbolic gain sets
    for both branches, then replays every combined witness on both branches. -/
def analyzeModelInteraction (model : Model) (baseRoot leftRoot rightRoot
    combinedRoot : String) (schema : Cedar.Validation.Schema) :
    IO (Except InteractionError InteractionReport) := do
  if baseRoot == leftRoot || baseRoot == rightRoot || leftRoot == rightRoot ||
      combinedRoot == baseRoot || combinedRoot == leftRoot || combinedRoot == rightRoot then
    return .error (.topology "the four roots must be distinct")
  let some combinedModule := model.modules.find? (·.name == combinedRoot)
    | return .error (.topology "combined root is absent")
  if combinedModule.parentOrders != [[leftRoot, rightRoot]] then
    return .error (.topology "combined root must directly mix the two branches")
  for branch in [leftRoot, rightRoot] do
    let ancestors ← match LeanPoo.C4.linearize model.graph branch with
      | .ok names => pure names
      | .error _ => return .error (.topology s!"invalid C4 branch: {branch}")
    if !ancestors.contains baseRoot then
      return .error (.topology s!"branch does not inherit base: {branch}")
  let left ← match ← analyzeModelExplained model baseRoot leftRoot schema with
    | .ok report => pure report
    | .error error => return .error (.delta error)
  let right ← match ← analyzeModelExplained model baseRoot rightRoot schema with
    | .ok report => pure report
    | .error error => return .error (.delta error)
  let combined ← match ← analyzeModelExplained model baseRoot combinedRoot schema with
    | .ok report => pure report
    | .error error => return .error (.delta error)
  let outcome ← if !left.symbolic.noExpansion || !right.symbolic.noExpansion then
      pure .branchExpanded
    else if combined.symbolic.noExpansion then
      pure .noCombinedGain
    else do
      let compiler := Functional.compilation model
      let leftPolicies ← match compiler.compile leftRoot with
        | .ok compiled => pure compiled.policies
        | .error error => return .error (.compilation error)
      let rightPolicies ← match compiler.compile rightRoot with
        | .ok compiled => pure compiled.policies
        | .error error => return .error (.compilation error)
      let mut witnesses := []
      for gain in combined.symbolic.expansions do
        let leftResponse := isAuthorized gain.witness.request gain.witness.entities leftPolicies
        let rightResponse := isAuthorized gain.witness.request gain.witness.entities rightPolicies
        if leftResponse.decision != .deny then
          return .error (.branchReplayAllowed leftRoot gain.witness)
        if rightResponse.decision != .deny then
          return .error (.branchReplayAllowed rightRoot gain.witness)
        witnesses := witnesses ++ [{ combined := gain, leftResponse, rightResponse }]
      pure (.jointOnlyGain witnesses)
  return .ok { baseRoot, left, right, combined, outcome }

end CedarPooSpec.Authorization.Delta
