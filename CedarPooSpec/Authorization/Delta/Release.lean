import CedarPooSpec.Authorization.Delta.Interaction
import CedarPooSpec.Admission.PolicySnapshot

/-!
Bind one four-root analysis to the exact POO declarations, Cedar schema,
compiled policies, and Host policy epoch. The Host must compare and reserve
these under its own transaction before publishing or executing a revision.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec Cedar.Validation CedarPooSpec.PolicyModules

private def sameActionEntry (left right : ActionSchemaEntry) : Bool :=
  decide (left.appliesToPrincipal = right.appliesToPrincipal ∧
    left.appliesToResource = right.appliesToResource ∧
    left.ancestors = right.ancestors ∧ left.context = right.context)

/-- Exact schema representation check. An order-only change may require
    reanalysis too; the release gate intentionally fails closed. -/
def sameSchema (left right : Schema) : Bool :=
  decide (left.ets = right.ets) &&
    left.acts.toList.length == right.acts.toList.length &&
    (left.acts.toList.zip right.acts.toList).all fun (a, b) =>
      a.1 == b.1 && sameActionEntry a.2 b.2

structure ReviewSnapshot where
  /-- Only modules in the four C4 ancestries; unrelated new owners do not
      invalidate an otherwise unchanged analysis. -/
  modules : List Module
  schema : Schema
  epoch : Nat
  base : CedarPooSpec.Admission.PolicySnapshot
  left : CedarPooSpec.Admission.PolicySnapshot
  right : CedarPooSpec.Admission.PolicySnapshot
  combined : CedarPooSpec.Admission.PolicySnapshot

/-- Captured only by analyzeAndCapture through the supported API. Read-only
projections remain public. This prevents ordinary record-splicing, not hostile
code using Lean's private-name internals or forged native serialized evidence. -/
structure ReviewedInteraction where
  private mk ::
  analysis : InteractionReport
  snapshot : ReviewSnapshot

inductive ReleaseError where
  | analysis (error : InteractionError)
  | compilation (error : PolicyModules.Error)
  | modelChanged
  | schemaChanged
  | epochChanged
  | activeRootChanged
  | activePoliciesChanged
  | notEnforcing
  | requiresReview
  | rootChanged (root : String) (error : CedarPooSpec.Admission.PolicySnapshot.Error)
  deriving Repr

private def relevantModules (model : Model) (roots : List String) :
    Except PolicyModules.Error (List Module) := do
  let chains ← roots.mapM fun root =>
    (LeanPoo.C4.linearize model.graph root).mapError PolicyModules.Error.c4
  let names := chains.flatten.eraseDups
  names.mapM fun name =>
    match model.modules.find? (·.name == name) with
    | some module => .ok module
    | none => .error (.missingModule name)

/-- Analyze the whole four-root state before capturing a release snapshot.
    A joint-only gain is still a review finding, not automatic approval. -/
def analyzeAndCapture (model : Model) (baseRoot leftRoot rightRoot combinedRoot : String)
    (schema : Schema) (epoch : Nat) : IO (Except ReleaseError ReviewedInteraction) := do
  let analysis ← match ← analyzeModelInteraction model baseRoot leftRoot rightRoot
      combinedRoot schema with
    | .ok report => pure report
    | .error error => return .error (.analysis error)
  let capture (root : String) : Except ReleaseError CedarPooSpec.Admission.PolicySnapshot :=
    (CedarPooSpec.Admission.PolicySnapshot.capture model root).mapError .compilation
  let snapshot ← match do
      let modules ← (relevantModules model
        [baseRoot, leftRoot, rightRoot, combinedRoot]).mapError ReleaseError.compilation
      let base ← capture baseRoot
      let left ← capture leftRoot
      let right ← capture rightRoot
      let combined ← capture combinedRoot
      pure ({ modules, schema, epoch, base, left, right, combined } :
        ReviewSnapshot) with
    | .ok value => pure value
    | .error error => return .error error
  return .ok { analysis, snapshot }

/-- Check the analyzed source state against the current Host epoch and model.
    A production Host must perform this comparison and its policy publication
    under one serialized transaction. This pure function does not publish. -/
def ReviewSnapshot.currentPolicies (snapshot : ReviewSnapshot) (model : Model)
    (schema : Schema) (epoch : Nat) : Except ReleaseError Policies := do
  if snapshot.epoch != epoch then throw .epochChanged
  let modules ← (relevantModules model [snapshot.base.root, snapshot.left.root,
    snapshot.right.root, snapshot.combined.root]).mapError ReleaseError.compilation
  if !decide (snapshot.modules = modules) then throw .modelChanged
  if !sameSchema snapshot.schema schema then throw .schemaChanged
  let check (item : CedarPooSpec.Admission.PolicySnapshot) :
      Except ReleaseError Policies :=
    item.currentPolicies model |>.mapError (.rootChanged item.root)
  let _ ← check snapshot.base
  let _ ← check snapshot.left
  let _ ← check snapshot.right
  check snapshot.combined

/-- Return the current composed policies only for a reviewed no-gain result.
    Joint gains and branch gains require a separate authenticated approval;
    this function never publishes or executes a policy. -/
def ReviewedInteraction.noGainCurrentPolicies (reviewed : ReviewedInteraction)
    (model : Model) (schema : Schema) (epoch : Nat) :
    Except ReleaseError Policies := do
  match reviewed.analysis.outcome with
  | .noCombinedGain => reviewed.snapshot.currentPolicies model schema epoch
  | .branchExpanded | .jointOnlyGain _ => .error .requiresReview

/-- Whether the Host actually enforces Cedar decisions at the effect boundary.
    Observation and bypass are distinct deployment states, not Cedar policy
    effects. -/
inductive ExecutionMode where
  | enforcing
  | observing
  | disabled
  deriving BEq, Repr

/-- Pure model of the Host's active policy version and execution mode. The
    Host owns durable storage and synchronization of this state. -/
structure ReleaseState where
  activeRoot : String
  activePolicies : Policies
  executionMode : ExecutionMode
  epoch : Nat
  deriving BEq, Repr

/-- A compare-and-swap transition for a no-gain candidate. A real Host must
    apply the version check, publication, and epoch increment atomically. -/
def ReviewedInteraction.advanceNoGain (reviewed : ReviewedInteraction)
    (model : Model) (schema : Schema) (state : ReleaseState) :
    Except ReleaseError (ReleaseState × Policies) := do
  if state.activeRoot != reviewed.snapshot.base.root then throw .activeRootChanged
  if state.activePolicies != reviewed.snapshot.base.policies then
    throw .activePoliciesChanged
  if state.executionMode != .enforcing then throw .notEnforcing
  let policies ← reviewed.noGainCurrentPolicies model schema state.epoch
  let next : ReleaseState :=
    { activeRoot := reviewed.snapshot.combined.root,
      activePolicies := policies, executionMode := .enforcing,
      epoch := state.epoch + 1 }
  return (next, policies)

end CedarPooSpec.Authorization.Delta
