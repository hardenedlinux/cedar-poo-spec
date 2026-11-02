import Tests.Gateway.Fixture
import LeanPoo.Functional.PropertyTesting
import CedarPooSpec.Functional.Capabilities

open CedarPooSpec CedarPooSpec.GatewayTest

private def checkedPlan (before after : String) : IO Gateway.DeltaPlan :=
  match Gateway.prepareDelta model before after schema scope scope with
  | .ok plan => pure plan
  | .error error => throw (IO.userError s!"Gateway Delta preparation: {repr error}")

private def analyzePlan (plan : Gateway.DeltaPlan) := do
  match ← plan.analyze with
  | .ok report => pure report
  | .error error => throw (IO.userError s!"Gateway Delta analysis: {repr error}")

-- The ordinary public analyzer, not a fabricated ReviewedInteraction.
private def releaseModel : PolicyModules.Model :=
  { modules := [
    { name := "base", edits := [.extend permitPolicy,
      .extend { denyPolicy with id := "risk" }, .extend { denyPolicy with id := "compliance" }] },
    { name := "left", parentOrders := [["base"]], edits := [.remove "risk"] },
    { name := "right", parentOrders := [["base"]], edits := [.remove "compliance"] },
    { name := "mixed", parentOrders := [["left", "right"]] },
    { name := "retained", parentOrders := [["base"]] },
    { name := "safe", parentOrders := [["left", "retained"]] }] }

-- A bounded simulated authority: the recovered active image and independent
-- epoch floor survive live-image rollback. This is a test store, not a claim
-- about disk anti-rollback. Unknown publication results survive lost replies.
private structure PublicationState where
  live : Authorization.Delta.ReleaseState
  durable : Authorization.Delta.ReleaseState
  floor : Nat
  unknown : Bool := false

private def publicationStep (reviewed : Authorization.Delta.ReviewedInteraction)
    (approved : Bool) (initial : Authorization.Delta.ReleaseState)
    (image : PublicationState) (command : Nat) : PublicationState × Nat :=
  if command == 0 || command == 6 then
    if image.live.epoch != image.floor then (image, 0) else
    match reviewed.advanceReviewed releaseModel schema image.live (fun _ _ => approved) with
    | .error _ => (image, 0)
    | .ok (next, _) =>
      (⟨next, next, next.epoch, image.unknown || command == 6⟩, if command == 6 then 2 else 1)
  else if command == 1 then
    ({image with live := {image.live with executionMode := .observing}, durable := {image.durable with executionMode := .observing}}, 0)
  else if command == 2 then
    ({image with live := {image.live with executionMode := .disabled}, durable := {image.durable with executionMode := .disabled}}, 0)
  else if command == 3 then ({image with live := image.durable}, 0)
  else if command == 4 then ({image with live := initial}, 0)
  else
    ({image with live := {image.live with executionMode := .enforcing}, durable := {image.durable with executionMode := .enforcing}}, 0)

-- This is a property of the actual simulator function, not an assumed step
-- relation. The independent floor is never reset by any declared command.
private theorem publicationStep_invariant
    (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (image : PublicationState) (command : Nat) :
    let result := publicationStep reviewed approved initial image command
    image.floor ≤ result.1.floor ∧
      (image.unknown = true → result.1.unknown = true) ∧
      (result.2 ≠ 0 → image.floor = reviewed.snapshot.epoch ∧
        result.1.floor = reviewed.snapshot.epoch + 1) := by
  unfold publicationStep
  split
  · split
    · simp
    · rename_i fresh
      cases accepted : reviewed.advanceReviewed releaseModel schema image.live (fun _ _ => approved) with
      | error error => simp
      | ok value =>
        obtain ⟨next, policies⟩ := value
        obtain ⟨epoch, rfl⟩ := reviewed.advanceReviewed_postcondition releaseModel schema image.live next policies
          (fun _ _ => approved) accepted
        cases lost : command == 6 <;> simp_all
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · split <;> simp

-- Induction over the existing released trace projection, with no horizon or
-- sample-count premise. The finite Rust corpus remains a separate conformance test.
private theorem publicationHistory_retired
    (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (commands : List Nat)
    (image : PublicationState) (retired : reviewed.snapshot.epoch < image.floor) :
    (LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationStep reviewed approved initial) id image commands).countP (fun row => row.1 != 0) = 0 := by
  induction commands generalizing image with
  | nil => rfl
  | cons command rest ih =>
    cases transition : publicationStep reviewed approved initial image command with
    | mk after reply =>
      have invariant := publicationStep_invariant reviewed approved initial image command
      simp only [transition] at invariant
      have zero : reply = 0 := by
        by_contra nonzero
        have committed := invariant.2.2 nonzero
        omega
      have nextRetired : reviewed.snapshot.epoch < after.floor := by omega
      simpa [LeanPoo.Functional.PropertyTesting.traceObservations, transition, zero] using ih after nextRetired

private theorem publicationHistory_at_most_one_commit
    (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (commands : List Nat) (image : PublicationState) :
    (LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationStep reviewed approved initial) id image commands).countP (fun row => row.1 != 0) ≤ 1 := by
  induction commands generalizing image with
  | nil => simp [LeanPoo.Functional.PropertyTesting.traceObservations]
  | cons command rest ih =>
    cases transition : publicationStep reviewed approved initial image command with
    | mk after reply =>
      by_cases zero : reply = 0
      · simpa [LeanPoo.Functional.PropertyTesting.traceObservations, transition, zero] using ih after
      · have invariant := publicationStep_invariant reviewed approved initial image command
        simp only [transition] at invariant
        have retired : reviewed.snapshot.epoch < after.floor := by
          have committed := invariant.2.2 zero
          omega
        have noMore := publicationHistory_retired reviewed approved initial rest after retired
        simp [LeanPoo.Functional.PropertyTesting.traceObservations, transition, zero, noMore]

private theorem publicationHistory_retains_unknown
    (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (commands : List Nat)
    (image : PublicationState) (held : image.unknown = true) :
    ∀ observation ∈ LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationStep reviewed approved initial) id image commands, observation.2.unknown = true := by
  induction commands generalizing image with
  | nil => simp [LeanPoo.Functional.PropertyTesting.traceObservations]
  | cons command rest ih =>
    cases transition : publicationStep reviewed approved initial image command with
    | mk after reply =>
      have invariant := publicationStep_invariant reviewed approved initial image command
      simp only [transition] at invariant
      have nextHeld := invariant.2.1 held
      intro observation member
      have located : observation = (reply, after) ∨ observation ∈
          LeanPoo.Functional.PropertyTesting.traceObservations
            (publicationStep reviewed approved initial) id after rest := by
        simpa [LeanPoo.Functional.PropertyTesting.traceObservations, transition] using member
      rcases located with rfl | later
      · exact nextHeld
      · exact ih after nextHeld observation later

#print axioms publicationStep_invariant
#print axioms publicationHistory_at_most_one_commit
#print axioms publicationHistory_retains_unknown

private def modeName : Authorization.Delta.ExecutionMode → String
  | .enforcing => "enforcing" | .observing => "observing" | .disabled => "disabled"

private def publicationObservation (image : PublicationState) : Lean.Json :=
  Lean.Json.mkObj [("root", Lean.toJson image.live.activeRoot), ("epoch", Lean.toJson image.live.epoch),
    ("mode", Lean.toJson (modeName image.live.executionMode)), ("floor", Lean.toJson image.floor),
    ("durable_root", Lean.toJson image.durable.activeRoot), ("durable_epoch", Lean.toJson image.durable.epoch),
    ("durable_mode", Lean.toJson (modeName image.durable.executionMode)), ("unknown", Lean.toJson image.unknown)]

private def publicationTraces (reviewed : Authorization.Delta.ReviewedInteraction)
    (approved : Bool) : IO Lean.Json := do
  let initial : Authorization.Delta.ReleaseState :=
    ⟨reviewed.snapshot.base.root, reviewed.snapshot.base.policies, .enforcing, 7⟩
  let start : PublicationState := ⟨initial, initial, 7, false⟩
  let noGain := match reviewed.analysis.outcome with | .noCombinedGain => true | _ => false
  if noGain || approved then
    let first := publicationStep reviewed approved initial start 0
    let rolled := publicationStep reviewed approved initial first.1 4
    let guarded :=  publicationStep reviewed approved initial rolled.1 0
    let weakened := publicationStep reviewed approved initial {rolled.1 with floor := 7} 0
    unless first.2 == 1 && guarded.2 == 0 && weakened.2 == 1 do
      throw (IO.userError "rollback negative control did not distinguish the independent authority floor")
  let traceModel : LeanPoo.Functional.PropertyTesting.TraceModel PublicationState Nat Nat :=
    ⟨start, (fun _ command => decide (command < 7)), publicationStep reviewed approved initial⟩
  let mut traces : Array Lean.Json := #[]
  for seed in LeanPoo.Functional.PropertyTesting.samples (fun seed _ => (seed, seed + 1)) 343 0 0 do
    let commands := [seed % 7, seed / 7 % 7, seed / 49 % 7]
    unless LeanPoo.Functional.PropertyTesting.traceValid traceModel start commands do
      throw (IO.userError s!"invalid generated publication trace {seed}")
    let observed := LeanPoo.Functional.PropertyTesting.traceObservations traceModel.advance id start commands
    let mut count := 0
    let mut held := false
    for (reply, state) in observed do
      if reply != 0 then count := count + 1
      unless decide (count ≤ 1) && (!held || state.unknown) do
        throw (IO.userError s!"publication replay/reset trace failed at {seed}")
      held := state.unknown
    traces := traces.push (Lean.Json.mkObj [("seed", Lean.toJson seed), ("commands", Lean.toJson commands),
      ("observations", Lean.toJson (observed.map fun (reply, state) => Lean.Json.mkObj [("reply", Lean.toJson reply), ("state", publicationObservation state)]))])
  return Lean.Json.mkObj [("base", Lean.toJson reviewed.snapshot.base.root),
    ("candidate", Lean.toJson reviewed.snapshot.combined.root), ("no_gain", Lean.toJson noGain),
    ("approved", Lean.toJson approved), ("traces", Lean.toJson traces)]

private def checkReleaseProperties : IO Unit := do
  let .ok gain ← Authorization.Delta.analyzeAndCapture releaseModel "base" "left" "right" "mixed" schema 7
    | throw (IO.userError "could not capture actual joint-gain analysis")
  let .jointOnlyGain _ := gain.analysis.outcome
    | throw (IO.userError "fixture did not exercise governed expansion")
  let .ok safe ← Authorization.Delta.analyzeAndCapture releaseModel "base" "left" "retained" "safe" schema 7
    | throw (IO.userError "could not capture actual no-gain analysis")
  let .noCombinedGain := safe.analysis.outcome
    | throw (IO.userError "retained hold was not no-gain")
  -- Complete Cartesian coverage: mode, epoch, parent, policies, schema,
  -- source and approval. Deterministic finite generation uses the released POO
  -- API; no random success is promoted into a universal proof.
  let samples := LeanPoo.Functional.PropertyTesting.samples
    (fun seed _ => (seed, seed + 1)) 192 0 0
  for reviewed in [gain, safe] do
    for sample in samples do
      let mode := match sample % 3 with
        | 0 => Authorization.Delta.ExecutionMode.enforcing
        | 1 => .observing
        | _ => .disabled
      let epoch := if sample / 3 % 2 == 0 then 7 else 8
      let root := if sample / 6 % 2 == 0 then "base" else "mixed"
      let policies := if sample / 12 % 2 == 0 then reviewed.snapshot.base.policies else []
      let actualSchema := if sample / 24 % 2 == 0 then schema else { schema with acts := Cedar.Data.Map.empty }
      let actualModel := if sample / 48 % 2 == 0 then releaseModel else { modules := [] }
      let approved := sample / 96 % 2 == 0
      let current : Authorization.Delta.ReleaseState := ⟨root, policies, mode, epoch⟩
      let result := reviewed.advanceReviewed actualModel actualSchema current
        (fun exact state => approved && exact.snapshot.epoch == 7 && state.epoch == 7)
      let valid := sample % 3 == 0 && sample / 3 % 2 == 0 && sample / 6 % 2 == 0 &&
        sample / 12 % 2 == 0 && sample / 24 % 2 == 0 && sample / 48 % 2 == 0
      let noGain := match reviewed.analysis.outcome with | .noCombinedGain => true | _ => false
      unless result.isOk == (valid && (noGain || approved)) do
        throw (IO.userError s!"release property failed at full replay sample {sample}")
      if let .ok (next, published) := result then
        unless next.epoch == 8 && next.activeRoot == reviewed.snapshot.combined.root &&
            next.activePolicies == published && published == reviewed.snapshot.combined.policies &&
            next.executionMode == .enforcing &&
            !(reviewed.advanceReviewed actualModel actualSchema next (fun _ _ => true)).isOk do
          throw (IO.userError s!"release post-state/replay property failed at {sample}")
  -- Export actual policy/input combinations through the shared Functional
  -- producer. The ordinary Rust authorizer checks these, independently of the
  -- generated release-state properties above.
  let mut traceRuns : Array Lean.Json := #[]
  for reviewed in [gain, safe] do
    for approved in [true, false] do
      traceRuns := traceRuns.push (← publicationTraces reviewed approved)
  IO.FS.createDirAll ".lake/build"
  IO.FS.writeFile ".lake/build/gateway-publication-traces.json"
    (Lean.Json.mkObj [("format_version", Lean.toJson (1 : Nat)), ("runs", Lean.toJson traceRuns)]).compress
  IO.println "GATEWAY-PUBLICATION-TRACES-OK: 1372 complete three-command traces / 4116 steps; lost reply, recovery, rollback, modes and retry"
  let program := Functional.deferProgram Functional.standard releaseModel schema
    (releaseModel.modules.map (·.name)) (by native_decide)
  let mut cases := []
  for root in ["base", "left", "right", "mixed", "safe"] do
    for fact in [true, false] do
      let name := s!"{root}-current-{fact}"
      let .ok receipt := program.authorizationCase name root root (request "invoke" fact) entities
        | throw (IO.userError s!"could not export {name}")
      cases := cases ++ [receipt]
  IO.FS.createDirAll ".lake/build"
  IO.FS.writeFile ".lake/build/gateway-current-review-manifest.json"
    (Lean.Json.mkObj [("cases", Lean.toJson cases)]).compress
  IO.println "GATEWAY-REVIEW-PROPERTIES-OK: 384 cases; actual gain/no-gain analyses; stale/mode/source/schema/approval/post-state/replay"

def main : IO Unit := do
  checkReleaseProperties
  let restriction ← checkedPlan "base" "restricted"
  let restrictive ← analyzePlan restriction
  unless restrictive.gains.isEmpty && !restrictive.losses.isEmpty do
    throw (IO.userError "Gateway freeze did not have exact loss-only execution Delta")
  let expansion ← checkedPlan "restricted" "base"
  let expanding ← analyzePlan expansion
  unless !expanding.gains.isEmpty && expanding.losses.isEmpty do
    throw (IO.userError "Gateway unfreeze did not expose execution-gain witnesses")
  let unchanged ← checkedPlan "base" "base"
  let same ← analyzePlan unchanged
  unless same.gains.isEmpty && same.losses.isEmpty do
    throw (IO.userError "Gateway identity revision changed execution")
  unless restriction.matchesCurrent model scope &&
      !restriction.matchesCurrent replacedModel scope &&
      !restriction.matchesCurrent model { scope with sourceCut := "source-2" } do
    throw (IO.userError "Gateway Delta accepted stale policies or source scope")
  IO.println s!"GATEWAY-DELTA-OK: {restrictive.environmentsChecked} environments; loss/gain/equivalence and stale binding controls"
