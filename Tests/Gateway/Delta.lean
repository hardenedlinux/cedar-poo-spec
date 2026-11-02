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

private def followupModel : PolicyModules.Model :=
  { modules := releaseModel.modules ++ [
    { name := "postLeft", parentOrders := [["mixed"]] },
    { name := "postRight", parentOrders := [["mixed"]] },
    { name := "postMixed", parentOrders := [["postLeft", "postRight"]] }] }

-- A bounded simulated authority: the recovered active image and independent
-- epoch floor survive live-image rollback. This is a test store, not a claim
-- about disk anti-rollback. Unknown publication results survive lost replies.
private structure PublicationState where
  live : Authorization.Delta.ReleaseState
  durable : Authorization.Delta.ReleaseState
  floor : Nat
  unknown : Bool := false

private def publicationStep (currentModel : PolicyModules.Model) (reviewed : Authorization.Delta.ReviewedInteraction)
    (approved : Bool) (initial : Authorization.Delta.ReleaseState)
    (image : PublicationState) (command : Nat) : PublicationState × Nat :=
  if command == 0 || command == 6 then
    if image.live.epoch != image.floor then (image, 0) else
    match reviewed.advanceReviewed currentModel schema image.live (fun _ _ => approved) with
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
    (currentModel : PolicyModules.Model) (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (image : PublicationState) (command : Nat) :
    let result := publicationStep currentModel reviewed approved initial image command
    image.floor ≤ result.1.floor ∧
      (image.unknown = true → result.1.unknown = true) ∧
      (result.2 ≠ 0 → image.floor = reviewed.snapshot.epoch ∧
        result.1.floor = reviewed.snapshot.epoch + 1) := by
  unfold publicationStep
  split
  · split
    · simp
    · rename_i fresh
      cases accepted : reviewed.advanceReviewed currentModel schema image.live (fun _ _ => approved) with
      | error error => simp
      | ok value =>
        obtain ⟨next, policies⟩ := value
        obtain ⟨epoch, rfl⟩ := reviewed.advanceReviewed_postcondition currentModel schema image.live next policies
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
      (publicationStep releaseModel reviewed approved initial) id image commands).countP (fun row => row.1 != 0) = 0 := by
  induction commands generalizing image with
  | nil => rfl
  | cons command rest ih =>
    cases transition : publicationStep releaseModel reviewed approved initial image command with
    | mk after reply =>
      have invariant := publicationStep_invariant releaseModel reviewed approved initial image command
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
      (publicationStep releaseModel reviewed approved initial) id image commands).countP (fun row => row.1 != 0) ≤ 1 := by
  induction commands generalizing image with
  | nil => simp [LeanPoo.Functional.PropertyTesting.traceObservations]
  | cons command rest ih =>
    cases transition : publicationStep releaseModel reviewed approved initial image command with
    | mk after reply =>
      by_cases zero : reply = 0
      · simpa [LeanPoo.Functional.PropertyTesting.traceObservations, transition, zero] using ih after
      · have invariant := publicationStep_invariant releaseModel reviewed approved initial image command
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
      (publicationStep releaseModel reviewed approved initial) id image commands, observation.2.unknown = true := by
  induction commands generalizing image with
  | nil => simp [LeanPoo.Functional.PropertyTesting.traceObservations]
  | cons command rest ih =>
    cases transition : publicationStep releaseModel reviewed approved initial image command with
    | mk after reply =>
      have invariant := publicationStep_invariant releaseModel reviewed approved initial image command
      simp only [transition] at invariant
      have nextHeld := invariant.2.1 held
      intro observation member
      have located : observation = (reply, after) ∨ observation ∈
          LeanPoo.Functional.PropertyTesting.traceObservations
            (publicationStep releaseModel reviewed approved initial) id after rest := by
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
    let first := publicationStep releaseModel reviewed approved initial start 0
    let rolled := publicationStep releaseModel reviewed approved initial first.1 4
    let guarded :=  publicationStep releaseModel reviewed approved initial rolled.1 0
    let weakened := publicationStep releaseModel reviewed approved initial {rolled.1 with floor := 7} 0
    unless first.2 == 1 && guarded.2 == 0 && weakened.2 == 1 do
      throw (IO.userError "rollback negative control did not distinguish the independent authority floor")
  let traceModel : LeanPoo.Functional.PropertyTesting.TraceModel PublicationState Nat Nat :=
    ⟨start, (fun _ command => decide (command < 7)), publicationStep releaseModel reviewed approved initial⟩
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

-- Prepared tickets are authority-issued observation cuts, independent of the
-- policy epoch. They survive caller retries; every authority control advances cut.
private structure PublicationSchedule where
  current : ZeroTrust.Observation PublicationState
  first : Option Nat := none
  second : Option Nat := none
  registered : Nat := 0

private def publicationScheduleStep (currentModel : PolicyModules.Model) (reviewed : Authorization.Delta.ReviewedInteraction)
    (approved : Bool) (initial : Authorization.Delta.ReleaseState) (faults : Nat)
    (schedule : PublicationSchedule) (command : Nat) : PublicationSchedule × Nat :=
  if command == 0 then ({schedule with first := some schedule.current.generation}, 0)
  else if command == 1 then ({schedule with second := some schedule.current.generation}, 0)
  else if command == 2 || command == 3 then
    let ticket := if command == 2 then schedule.first else schedule.second
    match ticket with
    | none => (schedule, 5)
    | some generation =>
      let lost := if command == 2 then faults % 2 == 1 else faults / 2 % 2 == 1
      let transition (image : PublicationState) : Except Nat (Nat × PublicationState) :=
        let (next, reply) := publicationStep currentModel reviewed approved initial image (if lost then 6 else 0)
        if reply == 0 then .error 4 else .ok (reply, next)
      match ZeroTrust.Observation.compareAndAdvance generation schedule.current 3 transition with
      | .error cause => (schedule, cause)
      | .ok (reply, next) => ({schedule with current := next}, reply)
  else
    let control := if command == 4 then 3 else if command == 5 then 4
      else if command == 6 then 1 else if command == 7 then 5 else 2
    let transition (image : PublicationState) : Except Nat (Nat × PublicationState) :=
      let (next, reply) := publicationStep currentModel reviewed approved initial image control
      .ok (reply, next)
    match ZeroTrust.Observation.compareAndAdvance schedule.current.generation schedule.current 3 transition with
    | .error cause => (schedule, cause)
    | .ok (reply, next) => ({schedule with current := next}, reply)

-- The prepared scheduler inherits the release invariant through the actual
-- compare-and-advance function. Preparations and refusals leave the cut intact;
-- controls and successful publications advance it, including equal-data ABA.
private theorem publicationScheduleStep_invariant
    (currentModel : PolicyModules.Model) (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (faults : Nat)
    (schedule : PublicationSchedule) (command : Nat) :
    let result := publicationScheduleStep currentModel reviewed approved initial faults schedule command
    schedule.current.generation ≤ result.1.current.generation ∧
      schedule.current.attributes.floor ≤ result.1.current.attributes.floor ∧
      (schedule.current.attributes.unknown = true → result.1.current.attributes.unknown = true) ∧
      (result.2 = 1 ∨ result.2 = 2 →
        schedule.current.attributes.floor = reviewed.snapshot.epoch ∧
        result.1.current.attributes.floor = reviewed.snapshot.epoch + 1) := by
  unfold publicationScheduleStep
  split
  · simp
  · split
    · simp
    · split
      · generalize captured : (if command == 2 then schedule.first else schedule.second) = ticket
        cases ticket with
        | none => simp
        | some generation =>
          cases accepted : ZeroTrust.Observation.compareAndAdvance generation schedule.current 3
              (fun image =>
                let (next, reply) := publicationStep currentModel reviewed approved initial image
                  (if (if command == 2 then faults % 2 == 1 else faults / 2 % 2 == 1) then 6 else 0)
                if reply == 0 then .error 4 else .ok (reply, next)) with
          | error cause =>
            simp only [accepted]
            by_cases stale : (schedule.current.generation != generation) = true
            · simp [ZeroTrust.Observation.compareAndAdvance, stale] at accepted
              subst cause; simp
            · cases underlying : publicationStep currentModel reviewed approved initial schedule.current.attributes
                  (if (if command == 2 then faults % 2 == 1 else faults / 2 % 2 == 1) then 6 else 0) with
              | mk image reply =>
                simp only [ZeroTrust.Observation.compareAndAdvance, stale, underlying] at accepted
                by_cases denied : reply = 0
                · simp [denied] at accepted
                  subst cause; simp
                · simp [denied] at accepted
          | ok pair =>
            obtain ⟨reply, next⟩ := pair
            simp only [accepted]
            have post := ZeroTrust.Observation.compareAndAdvance_postcondition _ _ _ _ _ _ accepted
            cases underlying : publicationStep currentModel reviewed approved initial schedule.current.attributes
                (if (if command == 2 then faults % 2 == 1 else faults / 2 % 2 == 1) then 6 else 0) with
            | mk image output =>
              have invariant := publicationStep_invariant currentModel reviewed approved initial schedule.current.attributes
                (if (if command == 2 then faults % 2 == 1 else faults / 2 % 2 == 1) then 6 else 0)
              simp only [underlying] at invariant post
              split at post
              · simp_all
              · simp only [Except.ok.injEq, Prod.mk.injEq] at post
                obtain ⟨_, ⟨rfl, imageEq⟩, generationEq⟩ := post
                exact ⟨by omega, imageEq ▸ invariant.1, imageEq ▸ invariant.2.1,
                  fun committed => imageEq ▸ invariant.2.2 (by omega)⟩
      · simp only [ZeroTrust.Observation.compareAndAdvance, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte]
        have invariant := publicationStep_invariant currentModel reviewed approved initial schedule.current.attributes
          (if command == 4 then 3 else if command == 5 then 4 else if command == 6 then 1
            else if command == 7 then 5 else 2)
        exact ⟨by omega, invariant.1, invariant.2.1,
          fun committed => invariant.2.2 (by omega)⟩

-- No horizon, actor-order, generation, initial-state or approval restriction.
-- The finite native corpus checks conformance, not these universal claims.
private theorem publicationScheduleHistory_retired
    (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (faults : Nat) (commands : List Nat)
    (schedule : PublicationSchedule) (retired : reviewed.snapshot.epoch < schedule.current.attributes.floor) :
    (LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationScheduleStep releaseModel reviewed approved initial faults) id schedule commands).countP
        (fun row => row.1 == 1 || row.1 == 2) = 0 := by
  induction commands generalizing schedule with
  | nil => rfl
  | cons command rest ih =>
    cases transition : publicationScheduleStep releaseModel reviewed approved initial faults schedule command with
    | mk after reply =>
      have invariant := publicationScheduleStep_invariant releaseModel reviewed approved initial faults schedule command
      simp only [transition] at invariant
      have absent : ¬ (reply = 1 ∨ reply = 2) := by
        intro committed
        have bound := invariant.2.2.2 committed
        omega
      have nextRetired : reviewed.snapshot.epoch < after.current.attributes.floor := by omega
      simpa [LeanPoo.Functional.PropertyTesting.traceObservations, transition, absent] using
        ih after nextRetired

private theorem publicationScheduleHistory_at_most_one_commit
    (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (faults : Nat) (commands : List Nat)
    (schedule : PublicationSchedule) :
    (LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationScheduleStep releaseModel reviewed approved initial faults) id schedule commands).countP
        (fun row => row.1 == 1 || row.1 == 2) ≤ 1 := by
  induction commands generalizing schedule with
  | nil => simp [LeanPoo.Functional.PropertyTesting.traceObservations]
  | cons command rest ih =>
    cases transition : publicationScheduleStep releaseModel reviewed approved initial faults schedule command with
    | mk after reply =>
      by_cases committed : reply = 1 ∨ reply = 2
      · have invariant := publicationScheduleStep_invariant releaseModel reviewed approved initial faults schedule command
        simp only [transition] at invariant
        have retired : reviewed.snapshot.epoch < after.current.attributes.floor := by
          have bound := invariant.2.2.2 committed
          omega
        have noMore := publicationScheduleHistory_retired reviewed approved initial faults rest after retired
        simp [LeanPoo.Functional.PropertyTesting.traceObservations, transition, committed, noMore]
      · simpa [LeanPoo.Functional.PropertyTesting.traceObservations, transition, committed] using ih after

private theorem publicationScheduleHistory_retains_unknown
    (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (faults : Nat) (commands : List Nat)
    (schedule : PublicationSchedule) (held : schedule.current.attributes.unknown = true) :
    ∀ observation ∈ LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationScheduleStep releaseModel reviewed approved initial faults) id schedule commands,
      observation.2.current.attributes.unknown = true := by
  induction commands generalizing schedule with
  | nil => simp [LeanPoo.Functional.PropertyTesting.traceObservations]
  | cons command rest ih =>
    cases transition : publicationScheduleStep releaseModel reviewed approved initial faults schedule command with
    | mk after reply =>
      have invariant := publicationScheduleStep_invariant releaseModel reviewed approved initial faults schedule command
      simp only [transition] at invariant
      have nextHeld := invariant.2.2.1 held
      intro observation member
      have located : observation = (reply, after) ∨ observation ∈
          LeanPoo.Functional.PropertyTesting.traceObservations
            (publicationScheduleStep releaseModel reviewed approved initial faults) id after rest := by
        simpa [LeanPoo.Functional.PropertyTesting.traceObservations, transition] using member
      rcases located with rfl | later
      · exact nextHeld
      · exact ih after nextHeld observation later

private theorem publicationScheduleHistory_generation_monotone
    (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (faults : Nat) (commands : List Nat)
    (schedule : PublicationSchedule) :
    ∀ observation ∈ LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationScheduleStep releaseModel reviewed approved initial faults) id schedule commands,
      schedule.current.generation ≤ observation.2.current.generation := by
  induction commands generalizing schedule with
  | nil => simp [LeanPoo.Functional.PropertyTesting.traceObservations]
  | cons command rest ih =>
    cases transition : publicationScheduleStep releaseModel reviewed approved initial faults schedule command with
    | mk after reply =>
      have invariant := publicationScheduleStep_invariant releaseModel reviewed approved initial faults schedule command
      simp only [transition] at invariant
      intro observation member
      have located : observation = (reply, after) ∨ observation ∈
          LeanPoo.Functional.PropertyTesting.traceObservations
            (publicationScheduleStep releaseModel reviewed approved initial faults) id after rest := by
        simpa [LeanPoo.Functional.PropertyTesting.traceObservations, transition] using member
      rcases located with rfl | later
      · exact invariant.1
      · exact Nat.le_trans invariant.1 (ih after observation later)

private theorem publicationScheduleHistory_refuses_retired_cut
    (reviewed : Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (faults : Nat) (commands : List Nat)
    (schedule : PublicationSchedule) (retired : generation < schedule.current.generation)
    (observation : Nat × PublicationSchedule)
    (member : observation ∈ LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationScheduleStep releaseModel reviewed approved initial faults) id schedule commands)
    (stale : Error) (transition : PublicationState → Except Error (Result × PublicationState)) :
    ZeroTrust.Observation.compareAndAdvance generation observation.2.current stale transition = .error stale := by
  have forward := publicationScheduleHistory_generation_monotone reviewed approved initial faults commands
    schedule observation member
  apply ZeroTrust.Observation.compareAndAdvance_stale
  omega

#print axioms publicationScheduleStep_invariant
#print axioms publicationScheduleHistory_at_most_one_commit
#print axioms publicationScheduleHistory_retains_unknown
#print axioms publicationScheduleHistory_generation_monotone
#print axioms publicationScheduleHistory_refuses_retired_cut

private def scheduleObservation (schedule : PublicationSchedule) : Lean.Json :=
  Lean.Json.mkObj [("generation", Lean.toJson schedule.current.generation),
    ("image", publicationObservation schedule.current.attributes),
    ("first", Lean.toJson schedule.first), ("second", Lean.toJson schedule.second)]

private def publicationCasTraces (reviewed : Authorization.Delta.ReviewedInteraction)
    (approved : Bool) : IO Lean.Json := do
  let initial : Authorization.Delta.ReleaseState :=
    ⟨reviewed.snapshot.base.root, reviewed.snapshot.base.policies, .enforcing, 7⟩
  let start : PublicationSchedule := ⟨⟨0, ⟨initial, initial, 7, false⟩⟩, none, none, 0⟩
  let orders := [[0, 2, 1, 3], [0, 1, 2, 3], [0, 1, 3, 2],
    [1, 3, 0, 2], [1, 0, 3, 2], [1, 0, 2, 3]]
  let mut inputs : Array (Nat × List Nat) := #[]
  for faults in [0, 1, 2, 3] do
    for order in orders do
      inputs := inputs.push (faults, order)
      for position in List.range 5 do
        for control in [4, 5, 6, 7, 8] do
          inputs := inputs.push (faults, order.take position ++ [control] ++ order.drop position)
    inputs := inputs.push (faults, [0, 6, 7, 2])
    inputs := inputs.push (faults, [0, 6, 7, 0, 2])
  let mut traces : Array Lean.Json := #[]
  for (faults, commands) in inputs do
    let traceModel : LeanPoo.Functional.PropertyTesting.TraceModel PublicationSchedule Nat Nat :=
      ⟨start, (fun _ command => decide (command < 9)), publicationScheduleStep releaseModel reviewed approved initial faults⟩
    unless LeanPoo.Functional.PropertyTesting.traceValid traceModel start commands do
      throw (IO.userError "invalid prepared-publication command")
    let observed := LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationScheduleStep releaseModel reviewed approved initial faults) id start commands
    let mut commits := 0
    let mut previous := start.current
    let mut observations : Array Lean.Json := #[]
    for (reply, next) in observed do
      if reply == 1 || reply == 2 then commits := commits + 1
      unless decide (commits ≤ 1) &&
          decide (previous.generation ≤ next.current.generation) &&
          decide (previous.attributes.floor ≤ next.current.attributes.floor) &&
          (!previous.attributes.unknown || next.current.attributes.unknown) do
        throw (IO.userError s!"prepared-publication invariant failed: {faults}/{commands}")
      previous := next.current
      observations := observations.push (Lean.Json.mkObj [("reply", Lean.toJson reply),
        ("state", scheduleObservation next), ("commits", Lean.toJson commits)])
    traces := traces.push (Lean.Json.mkObj [("faults", Lean.toJson faults),
      ("commands", Lean.toJson commands), ("observations", Lean.toJson observations)])
  let noGain := match reviewed.analysis.outcome with | .noCombinedGain => true | _ => false
  return Lean.Json.mkObj [("base", Lean.toJson reviewed.snapshot.base.root),
    ("candidate", Lean.toJson reviewed.snapshot.combined.root), ("no_gain", Lean.toJson noGain),
    ("approved", Lean.toJson approved), ("traces", Lean.toJson traces)]

-- Registration changes the same authority cut as policy/control writes. The
-- existing scheduler performs every actual publication against the selected
-- current review. This companion model does not replace the fixed-review corpus.
private def publicationRegistrationStep
    (reviewAt : Nat → Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (faults : Nat)
    (schedule : PublicationSchedule) (command : Nat) : PublicationSchedule × Nat :=
  if command < 9 then
    publicationScheduleStep (if schedule.registered == 2 then followupModel else releaseModel) (reviewAt schedule.registered) approved initial faults schedule command
  else
    match ZeroTrust.Observation.compareAndAdvance schedule.current.generation schedule.current 3
        (fun image => (.ok (0, image) : Except Nat (Nat × PublicationState))) with
    | .error cause => (schedule, cause)
    | .ok (reply, next) => ({schedule with current := next, registered := command - 9}, reply)

private theorem publicationRegistrationStep_invariant
    (reviewAt : Nat → Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (faults : Nat)
    (schedule : PublicationSchedule) (command : Nat) :
    let result := publicationRegistrationStep reviewAt approved initial faults schedule command
    schedule.current.generation ≤ result.1.current.generation ∧
      schedule.current.attributes.floor ≤ result.1.current.attributes.floor ∧
      (schedule.current.attributes.unknown = true → result.1.current.attributes.unknown = true) := by
  unfold publicationRegistrationStep
  split
  · have invariant := publicationScheduleStep_invariant
      (if schedule.registered == 2 then followupModel else releaseModel)
      (reviewAt schedule.registered) approved initial faults schedule command
    exact ⟨invariant.1, invariant.2.1, invariant.2.2.1⟩
  · simp [ZeroTrust.Observation.compareAndAdvance]

-- All registration/control/recovery commands participate in the preserved
-- frontier. This proves the monotonicity premise used by the public Final law;
-- a raw live epoch may still rewind and must pass the independent floor guard.
private theorem publicationRegistrationHistory_preserves_frontiers
    (reviewAt : Nat → Authorization.Delta.ReviewedInteraction) (approved : Bool)
    (initial : Authorization.Delta.ReleaseState) (faults : Nat) (commands : List Nat)
    (schedule : PublicationSchedule) :
    ∀ observation ∈ LeanPoo.Functional.PropertyTesting.traceObservations
      (publicationRegistrationStep reviewAt approved initial faults) id schedule commands,
      schedule.current.generation ≤ observation.2.current.generation ∧
      schedule.current.attributes.floor ≤ observation.2.current.attributes.floor ∧
      (schedule.current.attributes.unknown = true → observation.2.current.attributes.unknown = true) := by
  induction commands generalizing schedule with
  | nil => simp [LeanPoo.Functional.PropertyTesting.traceObservations]
  | cons command rest ih =>
    cases transition : publicationRegistrationStep reviewAt approved initial faults schedule command with
    | mk after reply =>
      have invariant := publicationRegistrationStep_invariant reviewAt approved initial faults schedule command
      simp only [transition] at invariant
      intro observation member
      have located : observation = (reply, after) ∨ observation ∈
          LeanPoo.Functional.PropertyTesting.traceObservations
            (publicationRegistrationStep reviewAt approved initial faults) id after rest := by
        simpa [LeanPoo.Functional.PropertyTesting.traceObservations, transition] using member
      rcases located with rfl | later
      · exact invariant
      · have next := ih after observation later
        exact ⟨Nat.le_trans invariant.1 next.1, Nat.le_trans invariant.2.1 next.2.1,
          fun held => next.2.2 (invariant.2.2 held)⟩

#print axioms publicationRegistrationStep_invariant
#print axioms publicationRegistrationHistory_preserves_frontiers

private def publicationRegistrationTraces
    (gain safe followup : Authorization.Delta.ReviewedInteraction) (approved : Bool) : IO Lean.Json := do
  let reviewAt := fun index => if index == 0 then gain else if index == 1 then safe else followup
  let initial : Authorization.Delta.ReleaseState :=
    ⟨gain.snapshot.base.root, gain.snapshot.base.policies, .enforcing, 7⟩
  let start : PublicationSchedule := ⟨⟨0, ⟨initial, initial, 7, false⟩⟩, none, none, 0⟩
  let orders := [[0, 2, 1, 3], [0, 1, 2, 3], [0, 1, 3, 2],
    [1, 3, 0, 2], [1, 0, 3, 2], [1, 0, 2, 3]]
  let mut inputs : Array (Nat × List Nat) := #[]
  for faults in [0, 1, 2, 3] do
    for order in orders do
      inputs := inputs.push (faults, order)
      for position in List.range 5 do
        for registration in [9, 10, 11] do
          inputs := inputs.push (faults, order.take position ++ [registration] ++ order.drop position)
    for commands in [[0, 2, 11, 0, 2, 4, 1, 3], [0, 1, 10, 2, 3, 0, 2, 4],
        [0, 2, 11, 0, 2, 9, 0, 2, 5, 2], [0, 10, 9, 2, 0, 2, 1, 3]] do
      inputs := inputs.push (faults, commands)
  let mut traces : Array Lean.Json := #[]
  let mut steps := 0
  for (faults, commands) in inputs do
    let traceModel : LeanPoo.Functional.PropertyTesting.TraceModel PublicationSchedule Nat Nat :=
      ⟨start, (fun _ command => decide (command < 12)),
        publicationRegistrationStep reviewAt approved initial faults⟩
    unless LeanPoo.Functional.PropertyTesting.traceValid traceModel start commands do
      throw (IO.userError "invalid review-registration command")
    let observed := LeanPoo.Functional.PropertyTesting.traceObservations traceModel.advance id start commands
    let mut previous := start.current
    let mut commits := #[0, 0, 0]
    let mut observations : Array Lean.Json := #[]
    for (reply, next) in observed do
      unless next.registered < 3 do throw (IO.userError "unregistered review index")
      if reply == 1 || reply == 2 then commits := commits.modify next.registered (· + 1)
      unless commits.all (fun count => decide (count ≤ 1)) &&
          decide (commits.foldl (· + ·) 0 ≤ 2) &&
          decide (previous.generation ≤ next.current.generation) &&
          decide (previous.attributes.floor ≤ next.current.attributes.floor) &&
          (!previous.attributes.unknown || next.current.attributes.unknown) do
        throw (IO.userError s!"review-registration invariant failed: {faults}/{commands}")
      previous := next.current
      observations := observations.push (Lean.Json.mkObj [("reply", Lean.toJson reply),
        ("state", Lean.Json.mkObj [("registered", Lean.toJson next.registered),
          ("schedule", scheduleObservation next)]), ("commits", Lean.toJson commits)])
      steps := steps + 1
    traces := traces.push (Lean.Json.mkObj [("faults", Lean.toJson faults),
      ("commands", Lean.toJson commands), ("observations", Lean.toJson observations)])
  unless traces.size == 400 && steps == 2032 do throw (IO.userError "incomplete registration corpus")
  let reviews := [gain, safe, followup] |>.map fun reviewed =>
    Lean.Json.mkObj [("base", Lean.toJson reviewed.snapshot.base.root),
      ("candidate", Lean.toJson reviewed.snapshot.combined.root),
      ("epoch", Lean.toJson reviewed.snapshot.epoch), ("approved", Lean.toJson approved),
      ("no_gain", Lean.toJson (match reviewed.analysis.outcome with | .noCombinedGain => true | _ => false))]
  return Lean.Json.mkObj [("reviews", Lean.toJson reviews), ("traces", Lean.toJson traces)]

private def checkReleaseProperties : IO Unit := do
  let .ok gain ← Authorization.Delta.analyzeAndCapture releaseModel "base" "left" "right" "mixed" schema 7
    | throw (IO.userError "could not capture actual joint-gain analysis")
  let .jointOnlyGain _ := gain.analysis.outcome
    | throw (IO.userError "fixture did not exercise governed expansion")
  let .ok safe ← Authorization.Delta.analyzeAndCapture releaseModel "base" "left" "retained" "safe" schema 7
    | throw (IO.userError "could not capture actual no-gain analysis")
  let .noCombinedGain := safe.analysis.outcome
    | throw (IO.userError "retained hold was not no-gain")
  let .ok followup ← Authorization.Delta.analyzeAndCapture followupModel "mixed" "postLeft" "postRight" "postMixed" schema 8
    | throw (IO.userError "could not capture current follow-up review")
  let .noCombinedGain := followup.analysis.outcome
    | throw (IO.userError "identity follow-up was not no-gain")
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
  let mut casRuns : Array Lean.Json := #[]
  for reviewed in [gain, safe] do
    for approved in [true, false] do
      casRuns := casRuns.push (← publicationCasTraces reviewed approved)
  IO.FS.writeFile ".lake/build/gateway-publication-cas.json"
    (Lean.Json.mkObj [("format_version", Lean.toJson (1 : Nat)), ("runs", Lean.toJson casRuns)]).compress
  IO.println "GATEWAY-PUBLICATION-CAS-OK: 2528 histories / 12528 steps; all two-actor interleavings, control boundaries and ABA"
  let mut registrationRuns : Array Lean.Json := #[]
  for approved in [true, false] do
    registrationRuns := registrationRuns.push (← publicationRegistrationTraces gain safe followup approved)
  IO.FS.writeFile ".lake/build/gateway-publication-registration.json"
    (Lean.Json.mkObj [("format_version", Lean.toJson (1 : Nat)), ("runs", Lean.toJson registrationRuns)]).compress
  IO.println "GATEWAY-PUBLICATION-REGISTRATION-OK: 800 histories / 4064 steps; current review replacement, ABA and two legal publications"
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
  let followupProgram := Functional.deferProgram Functional.standard followupModel schema
    (followupModel.modules.map (·.name)) (by native_decide)
  let mut followupCases := []
  for root in ["postLeft", "postRight", "postMixed"] do
    for fact in [true, false] do
      let .ok receipt := followupProgram.authorizationCase s!"{root}-current-{fact}" root root
          (request "invoke" fact) entities
        | throw (IO.userError s!"could not export follow-up {root}")
      followupCases := followupCases ++ [receipt]
  IO.FS.writeFile ".lake/build/gateway-registration-manifest.json"
    (Lean.Json.mkObj [("cases", Lean.toJson followupCases)]).compress

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
