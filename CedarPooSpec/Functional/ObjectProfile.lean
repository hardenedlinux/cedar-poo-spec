import LeanPoo.Object.Definition
import LeanPoo.C4.ValidationInvariant
import LeanPoo.Functional.ObjectContractRefinement
import LeanPoo.Functional.CertifiedConsumer

/-! Shared typed-object admission. Contract and projection providers are selected
before observing an object. Their results retain its exact contract and reads. -/
namespace CedarPooSpec.Functional.ObjectProfile
open LeanPoo LeanPoo.Functional LeanPoo.Functional.ObjectContract

variable {Key : Type} {Value : Key → Type} [DecidableEq Key]
  [BEq Key] [LawfulBEq Key] [Hashable Key]

abbrev Object (Key : Type) (Value : Key → Type) [BEq Key] [LawfulBEq Key] [Hashable Key] :=
  LeanPoo.Object.Memoized Key Value
abbrev Check (Key : Type) (Value : Key → Type) [BEq Key] [LawfulBEq Key] [Hashable Key] :=
  Contract (Object Key Value) Key Unit String

/-- Static dependent slots need presence/inventory checks, not dynamic casts. -/
def shape (keys : List Key) : Check Key Value where
  view := {
    isObject := fun _ => true
    prototype := fun _ => true
    names := fun profile => LeanPoo.allSlots profile.plan
    lookup := fun profile key => (profile.read key).map fun _ => () }
  fields := keys.map fun key => { name := key, check := fun _ _ => [] }
  strict := true
  constraints := []
  obligations := fun _ _ => []
  validInventory := Or.inl rfl

structure Checked (contract : Check Key Value) (profile : Object Key Value) : Prop where
  accepted : diagnose contract profile [] = []

abbrev Projection (profile : Object Key Value) (key : Key) :=
  { value : Value key // profile.read key = some value }

inductive Capability where
  | check | project
  deriving DecidableEq, Repr

abbrev Result (contract : Check Key Value) (profile : Object Key Value) : Capability → Type
  | .check => Except (List (Issue Key String)) (PLift (Checked contract profile))
  | .project => Checked contract profile → (key : Key) → Option (Projection profile key)

abbrev Operations (contract : Check Key Value) :=
  Provider (Object Key Value) Capability (Result contract)

def check (contract : Check Key Value) (profile : Object Key Value) :
    Except (List (Issue Key String)) (PLift (Checked contract profile)) :=
  if valid : diagnose contract profile [] = [] then .ok ⟨⟨valid⟩⟩
  else .error (diagnose contract profile [])

def project (profile : Object Key Value) (key : Key) : Option (Projection profile key) :=
  match actual : profile.read key with
  | none => none
  | some value => some ⟨value, actual⟩

/-- Separate owners contribute executable contract admission and exact projection. -/
def providers (contract : Check Key Value) (owner : String) : Operations contract
  | .check => if owner == "Contract" then some (check contract) else none
  | .project => if owner == "Projection" then some (fun profile _ key => project profile key) else none

def graph : C4.Graph := { nodes := [
  { name := "Profile", parentOrders := [["Contract", "Projection"]] },
  { name := "Contract" }, { name := "Projection" }] }

private def contractCertificate :=
  (C4.certifyNodeReference "Contract" [] [] []).toOption.get (by decide)
private def projectionCertificate :=
  (C4.certifyNodeReference "Projection" [] [] []).toOption.get (by decide)
private def rootCertificate :=
  (C4.certifyNodeReference "Profile"
    [["Contract"], ["Projection"], ["Contract", "Projection"]] [[], []] []).toOption.get (by decide)

private theorem contractTrace : C4.GraphTrace graph "Contract" ["Contract"] [] :=
  C4.GraphTrace.node (node := { name := "Contract" }) rfl [] rfl (by simp) contractCertificate
private theorem projectionTrace : C4.GraphTrace graph "Projection" ["Projection"] [] :=
  C4.GraphTrace.node (node := { name := "Projection" }) rfl [] rfl (by simp) projectionCertificate
private theorem rootTrace : C4.GraphTrace graph "Profile" ["Profile", "Contract", "Projection"] [] := by
  apply C4.GraphTrace.node (node := { name := "Profile", parentOrders := [["Contract", "Projection"]] })
    rfl [("Contract", (["Contract"], [])), ("Projection", (["Projection"], []))] rfl _ rootCertificate
  intro row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact contractTrace
  · exact projectionTrace

/-- Kernel-certified graph derivation; no native computation axiom is admitted. -/
def order : C4.VerifiedOrder graph "Profile" where
  output := ["Profile", "Contract", "Projection"]
  accepted := C4.linearizeChecked_unique_complete rootTrace
    (C4.LinearizeState.reachableUnique_of_global (by decide))
  derivation := ⟨[], rootTrace⟩

def standard (contract : Check Key Value) : Operations contract :=
  LeanPoo.Functional.assemble order (providers contract)

abbrev required : List Capability := [.check, .project]
abbrev Data (contract : Check Key Value) (profile : Object Key Value) :=
  Requirements.Results (Result contract) profile required

/-- A selected projection cannot substitute a different object or field value. -/
def Coherent (contract : Check Key Value) (profile : Object Key Value)
    (data : Data contract profile) : Prop :=
  ∀ checked key value, data.2.1 checked key = some value → profile.read key = some value.val

theorem coherent (contract : Check Key Value) (profile : Object Key Value)
    (data : Data contract profile) : Coherent contract profile data := by
  intro _ _ value _
  exact value.property

structure Access (contract : Check Key Value) (profile : Object Key Value) where
  checked : PLift (Checked contract profile)
  project : (key : Key) → Option (Projection profile key)

def construct (contract : Check Key Value) (profile : Object Key Value)
    (data : Data contract profile) (_ : Coherent contract profile data) :
    Except (List (Issue Key String)) (Access contract profile) := do
  let checked ← data.1
  return ⟨checked, data.2.1 checked.down⟩

def prepare (contract : Check Key Value) (operations : Operations contract) :=
  Requirements.prepareConsumer operations required (Coherent contract)
    (fun _ _ profile => coherent contract profile _) (construct contract)

/-- Missing capability refusal precedes any object checks or callback execution. -/
theorem prepare_missing (contract : Check Key Value) (operations : Operations contract)
    (key : Capability) :
    prepare contract operations = .error key ↔ Requirements.prepare operations required = .error key :=
  Requirements.prepareConsumer_error_iff _ _ _ _ _ key

def read (contract : Check Key Value) (profile : Object Key Value) (key : Key) : Option (Value key) := do
  let factory ← (prepare contract (standard contract)).toOption
  let access ← (factory profile).toOption
  return (← access.project key).val

theorem read_requires_contract (contract : Check Key Value) (profile : Object Key Value)
    (key : Key) (value : Value key) (accepted : read contract profile key = some value) :
    diagnose contract profile [] = [] := by
  unfold read at accepted
  cases preparation : (prepare contract (standard contract)).toOption with
  | none => simp [preparation] at accepted
  | some factory =>
    cases admission : (factory profile).toOption with
    | none => simp [preparation, admission] at accepted
    | some access => exact access.checked.down.accepted

/-- Every exposed value is the actual inherited read, never provider metadata. -/
theorem read_matches_projection (contract : Check Key Value) (profile : Object Key Value)
    (key : Key) (value : Value key) (accepted : read contract profile key = some value) :
    profile.read key = some value := by
  unfold read at accepted
  cases preparation : (prepare contract (standard contract)).toOption with
  | none => simp [preparation] at accepted
  | some factory =>
    cases admission : (factory profile).toOption with
    | none => simp [preparation, admission] at accepted
    | some access =>
      cases projection : access.project key with
      | none => simp [preparation, admission, projection] at accepted
      | some actual =>
        have same : actual.val = value := by simpa [preparation, admission, projection] using accepted
        exact same ▸ actual.property

theorem read_rejected (contract : Check Key Value) (profile : Object Key Value)
    (key : Key) (rejected : diagnose contract profile [] ≠ []) :
    read contract profile key = none := by
  cases result : read contract profile key with
  | none => rfl
  | some value => exact False.elim (rejected (read_requires_contract contract profile key value result))

/-- Refining a domain contract cannot recover a value refused by its parent. -/
theorem refinement_preserves_rejection (contract : Check Key Value)
    (additional : Object Key Value → List Key → List (Issue Key String))
    (profile : Object Key Value) (key : Key) (rejected : diagnose contract profile [] ≠ []) :
    read (refine contract additional) profile key = none :=
  read_rejected _ profile key (refine_preserves_rejection contract additional profile [] rejected)

end CedarPooSpec.Functional.ObjectProfile
