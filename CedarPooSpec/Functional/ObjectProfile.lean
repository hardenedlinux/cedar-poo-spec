import CedarPooSpec.Functional.PreparedDiagnostics
import LeanPoo.Object.Dataflow
import LeanPoo.C4.ValidationInvariant
import LeanPoo.Functional.ObjectContractRefinement
import LeanPoo.Functional.CertifiedConsumer

/-! Shared typed-object admission. Contract and projection providers are selected
before observing an object. Their results retain its exact contract and reads. -/
namespace CedarPooSpec.Functional.ObjectProfile
open LeanPoo LeanPoo.Functional LeanPoo.Functional.ObjectContract

variable {Key : Type} {Value : Key → Type} [DecidableEq Key]
  [BEq Key] [LawfulBEq Key] [Hashable Key]

abbrev Object (Key : Type) (Value : Key → Type) [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key] :=
  LeanPoo.Object.Dataflow.Instance Key Value
abbrev Check (Key : Type) (Value : Key → Type) [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key] :=
  Contract (Object Key Value) Key Unit String

/-- Static dependent slots need presence/inventory checks, not dynamic casts. -/
def shape (keys : List Key) : Check Key Value where
  view := {
    isObject := fun _ => true
    prototype := fun _ => true
    names := LeanPoo.Object.Dataflow.Instance.slotNames
    lookup := fun profile key => (profile.read key).map fun _ => () }
  fields := keys.map fun key => { name := key, check := fun _ _ => [] }
  strict := true
  constraints := []
  obligations := fun _ _ => []
  validInventory := Or.inl rfl

/-- All domain objects retain the actual source-bound materialized closure. -/
theorem materialized_read (profile : Object Key Value) (key : Key) :
    profile.read key = (profile.template.scheduled.closed.raw key).bind Except.toOption :=
  profile.read_reference key

theorem materialized_inventory (profile : Object Key Value) :
    profile.slotNames = LeanPoo.allSlots profile.plan := profile.slotNames_exact

theorem materialized_source (profile : Object Key Value) :
    profile.template.plan.schema = profile.template.source.schema := profile.template.sourceAligned

/-- Retained C4 metadata is the lowering of the actual raw declaration at every name. -/
theorem materialized_lowering (profile : Object Key Value) (name : String) :
    profile.template.plan.schema.declaration name =
      (profile.template.source.declaration name).map LeanPoo.Object.Dataflow.Declaration.metadata := by
  rw [profile.template.sourceAligned]
  exact profile.template.source.schema_declaration name

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

def check (contract : Check Key Value) : (profile : Object Key Value) →
    Except (List (Issue Key String)) (PLift (Checked contract profile)) :=
  let prepared := prepareDiagnostics contract
  fun profile =>
    let report := prepared.report profile
    if valid : report = [] then .ok ⟨⟨(prepared.aligned profile).symm.trans valid⟩⟩
    else .error report

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

/-- Specialize the fixed certified order once by capability. Custom provider
assemblies still use prepare; the standard callbacks and object demands are exact. -/
def standard (contract : Check Key Value) : Operations contract
  | .check => some (check contract)
  | .project => some (fun profile _ key => project profile key)

/-- The static specialization is the original Functional/C4 provider selection,
including its actual factory functions, not merely equivalent returned values. -/
theorem standard_eq_assemble (contract : Check Key Value) :
    standard contract = LeanPoo.Functional.assemble order (providers contract) := by
  funext capability
  cases capability <;> rfl

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

/-- Retain selection independently of the actual immutable object being admitted. -/
def factory (contract : Check Key Value) :
    Factory (Object Key Value) (fun profile => Except (List (Issue Key String)) (Access contract profile)) :=
  (prepare contract (standard contract)).toOption.get (by rfl)

def admit? (contract : Check Key Value) (profile : Object Key Value) : Option (Access contract profile) :=
  (factory contract profile).toOption

/-- Read any number of fields from the same admitted object without re-diagnosing it. -/
def Access.read {contract : Check Key Value} {profile : Object Key Value} (access : Access contract profile) (key : Key) : Option (Value key) :=
  (access.project key).map Subtype.val

theorem Access.read_matches {contract : Check Key Value} {profile : Object Key Value} (access : Access contract profile) (key : Key) (value : Value key)
    (found : access.read key = some value) : profile.read key = some value := by
  unfold Access.read at found
  cases result : access.project key with
  | none => simp [result] at found
  | some actual =>
    have same : actual.val = value := by simpa [result] using found
    exact same ▸ actual.property

theorem Access.accepted {contract : Check Key Value} {profile : Object Key Value} (access : Access contract profile) : diagnose contract profile [] = [] :=
  access.checked.down.accepted

/-- A retained admission is additionally indexed by the actual selected factory.
No decidable equality over functions or nominal provider labels is assumed. -/
structure Session (contract : Check Key Value)
    (family : Factory (Object Key Value) (fun profile => Except (List (Issue Key String)) (Access contract profile)))
    (profile : Object Key Value) where
  access : Access contract profile
  produced : family profile = .ok access

def Session.open (contract : Check Key Value)
    (family : Factory (Object Key Value) (fun profile => Except (List (Issue Key String)) (Access contract profile)))
    (profile : Object Key Value) : Except (List (Issue Key String)) (Session contract family profile) :=
  match result : family profile with
  | .error issues => .error issues
  | .ok access => .ok ⟨access, result⟩

def Session.read {contract : Check Key Value} {family} {profile : Object Key Value}
    (session : Session contract family profile) (key : Key) : Option (Value key) :=
  session.access.read key

theorem Session.read_matches {contract : Check Key Value} {family} {profile : Object Key Value}
    (session : Session contract family profile) (key : Key) (value : Value key)
    (found : session.read key = some value) : profile.read key = some value :=
  session.access.read_matches key value found


theorem Session.no_session_if_refused (contract : Check Key Value)
    (family : Factory (Object Key Value) (fun profile => Except (List (Issue Key String)) (Access contract profile)))
    (profile : Object Key Value) (issues : List (Issue Key String))
    (refused : family profile = .error issues) : ¬ Nonempty (Session contract family profile) := by
  intro ⟨session⟩
  have impossible := session.produced.symm.trans refused
  cases impossible

def read (contract : Check Key Value) (profile : Object Key Value) (key : Key) : Option (Value key) :=
  (prepare contract (standard contract)).toOption.bind fun factory =>
    (factory profile).toOption.bind fun access => (access.project key).map Subtype.val

/-- Batch projection has exactly the original optional value, including absence/refusal. -/
theorem admit_read_eq (contract : Check Key Value) (profile : Object Key Value) (key : Key) :
    ((admit? contract profile).bind fun access => access.read key) = read contract profile key := by
  have prepared : (prepare contract (standard contract)).toOption = some (factory contract) := by rfl
  cases result : (factory contract profile).toOption with
  | none => simp [admit?, read, prepared, result]
  | some access =>
    cases projection : access.project key <;> simp [admit?, Access.read, read, prepared, result, projection]

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
