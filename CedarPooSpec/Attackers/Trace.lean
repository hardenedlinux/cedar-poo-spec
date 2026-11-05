/-! An explicit attacker view of a supplied application boundary. Acquisition
rules describe the assumed compromise graph; they do not discover exploits.
The application's existing checked writer remains the only effect producer.
Denied acquisition/call attempts are retained in the executable trace. -/
namespace CedarPooSpec.Attackers

structure Rule (Capability : Type) where
  requires : List Capability
  grants : Capability
  deriving DecidableEq, Repr

structure Surface (Capability Request World Output : Type) where
  rules : List (Rule Capability)
  reachable : List Capability → Request → Bool
  invoke : World → Request → Option (World × Output)

inductive Action (Capability Request : Type) where
  | acquire (capability : Capability)
  | call (request : Request)

structure State (Capability World Output : Type) where
  known : List Capability
  world : World
  outputs : List Output := []
  refused : Nat := 0

variable [DecidableEq Capability]

def Rule.enabled (rule : Rule Capability) (known : List Capability) (target : Capability) : Bool :=
  decide (rule.grants = target) && rule.requires.all (fun cap => decide (cap ∈ known))

def learnable (surface : Surface Capability Request World Output)
    (known : List Capability) (target : Capability) : Bool :=
  surface.rules.any (fun rule => rule.enabled known target)

def step (surface : Surface Capability Request World Output)
    (state : State Capability World Output) (action : Action Capability Request) :
    State Capability World Output :=
  match action with
  | .acquire capability =>
      if learnable surface state.known capability then
        { state with known := capability :: state.known }
      else { state with refused := state.refused + 1 }
  | .call request =>
      if surface.reachable state.known request then
        match surface.invoke state.world request with
        | none => { state with refused := state.refused + 1 }
        | some (world, output) => { state with world, outputs := state.outputs ++ [output] }
      else { state with refused := state.refused + 1 }

def run (surface : Surface Capability Request World Output)
    (state : State Capability World Output) : List (Action Capability Request) →
    State Capability World Output
  | [] => state
  | action :: actions => run surface (step surface state action) actions

theorem learnable_has_rule (surface : Surface Capability Request World Output)
    (known : List Capability) (target : Capability)
    (enabled : learnable surface known target = true) :
    ∃ rule ∈ surface.rules, rule.grants = target ∧
      ∀ cap ∈ rule.requires, cap ∈ known := by
  obtain ⟨rule, member, enabled⟩ := List.any_eq_true.mp enabled
  have parts := Bool.and_eq_true_iff.mp enabled
  exact ⟨rule, member, of_decide_eq_true parts.1,
    fun cap member => of_decide_eq_true (List.all_eq_true.mp parts.2 cap member)⟩

theorem step_preserves_absence (surface : Surface Capability Request World Output)
    (isolated : Capability) (notGranted : ∀ rule ∈ surface.rules, rule.grants ≠ isolated)
    (state : State Capability World Output) (absent : isolated ∉ state.known)
    (action : Action Capability Request) : isolated ∉ (step surface state action).known := by
  cases action with
  | acquire capability =>
      cases enabled : learnable surface state.known capability with
      | false => simpa [step, enabled] using absent
      | true =>
          obtain ⟨rule, member, grant, _⟩ := learnable_has_rule surface state.known capability enabled
          have different : isolated ≠ capability := by
            intro same
            exact notGranted rule member (grant.trans same.symm)
          simpa [step, enabled, different] using absent
  | call request =>
      cases reachable : surface.reachable state.known request with
      | false => simpa [step, reachable] using absent
      | true =>
          cases invoked : surface.invoke state.world request with
          | none => simpa [step, reachable, invoked] using absent
          | some pair => simpa [step, reachable, invoked] using absent

/-- Arbitrary finite action sequences cannot manufacture an independent trust
root absent from both the initial compromise and the assumed acquisition graph. -/
theorem run_preserves_absence (surface : Surface Capability Request World Output)
    (isolated : Capability) (notGranted : ∀ rule ∈ surface.rules, rule.grants ≠ isolated)
    (state : State Capability World Output) (absent : isolated ∉ state.known)
    (actions : List (Action Capability Request)) :
    isolated ∉ (run surface state actions).known := by
  induction actions generalizing state with
  | nil => exact absent
  | cons action actions ih =>
      exact ih (step surface state action)
        (step_preserves_absence surface isolated notGranted state absent action)

theorem step_preserves_outputs (surface : Surface Capability Request World Output)
    (safe : Output → Prop)
    (writer : ∀ world request next output,
      surface.invoke world request = some (next, output) → safe output)
    (state : State Capability World Output) (prior : ∀ output ∈ state.outputs, safe output)
    (action : Action Capability Request) :
    ∀ output ∈ (step surface state action).outputs, safe output := by
  cases action with
  | acquire capability =>
      cases enabled : learnable surface state.known capability <;>
        simpa [step, enabled] using prior
  | call request =>
      cases reachable : surface.reachable state.known request with
      | false => simpa [step, reachable] using prior
      | true =>
          cases invoked : surface.invoke state.world request with
          | none => simpa [step, reachable, invoked] using prior
          | some pair =>
              rcases pair with ⟨next, result⟩
              have resultSafe := writer state.world request next result invoked
              simpa [step, reachable, invoked, List.mem_append, List.mem_singleton] using
                (show ∀ output, output ∈ state.outputs ∨ output = result → safe output from
                  fun output member => member.elim (prior output) (fun same => same.symm ▸ resultSafe))

/-- The application discharges `writer` for its actual transition, rather than
postulating that all requests are authorized. Complete mediation of physical
effects by that transition remains an explicit Host premise. -/
theorem run_preserves_outputs (surface : Surface Capability Request World Output)
    (safe : Output → Prop)
    (writer : ∀ world request next output,
      surface.invoke world request = some (next, output) → safe output)
    (state : State Capability World Output) (prior : ∀ output ∈ state.outputs, safe output)
    (actions : List (Action Capability Request)) :
    ∀ output ∈ (run surface state actions).outputs, safe output := by
  induction actions generalizing state with
  | nil => exact prior
  | cons action actions ih =>
      exact ih (step surface state action)
        (step_preserves_outputs surface safe writer state prior action)

/-- The application owner fixes the required output meaning. A graph certificate
alone is not a writer certificate; constructing this adapter requires its law.
This is neither an affine effect token nor physical mediation evidence. -/
structure CheckedWriter (Request World Output : Type) (required : Output → Prop) where
  invoke : World → Request → Option (World × Output)
  preserves : ∀ world request next output,
    invoke world request = some (next, output) → required output

end CedarPooSpec.Attackers
