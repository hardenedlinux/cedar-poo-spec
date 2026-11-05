import CedarPooSpec.Scenarios.Metadata
import LeanPoo.Functional.DeclarativeMetadata

/-! Functional scenario construction around existing typed models. Metadata is
mandatory; derivation retains exact parent provenance and delegates model
composition to the existing domain/POO owners. There is no scenario loader. -/
namespace CedarPooSpec.Scenarios
open LeanPoo.Functional.DeclarativeMetadata

structure Scenario (Model : Type) where
  metadata : CertifiedMetadata
  model : Model
  ancestors : List Metadata := []

def create (metadata : Metadata) (model : Model) : Except String (Scenario Model) :=
  if valid : metadata.valid = true then .ok ⟨⟨metadata, valid⟩, model, []⟩
  else .error "invalid scenario metadata"

def derive (parent : Scenario Parent) (metadata : Metadata) (bind : Parent → Model) :
    Except String (Scenario Model) :=
  if metadata.id ∈ (parent.metadata.value :: parent.ancestors).map Metadata.id then
    .error "scenario identifier already belongs to its ancestry"
  else
    match create metadata (bind parent.model) with
    | .error error => .error error
    | .ok child => .ok { child with ancestors := parent.metadata.value :: parent.ancestors }

def metadataContract : Contract Unit Metadata Metadata where
  input := ⟨"scenario-metadata", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"retained-scenario-metadata", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => input.valid = true ∧ result = input
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepareMetadata (metadata : Metadata) : Except String (Metadata × Unit) :=
  if metadata.valid then .ok (metadata, ()) else .error "invalid scenario metadata"

theorem invocation_retains_metadata (receipt : Invocation metadataContract prepareMetadata metadata) :
    metadata.valid = true ∧ receipt.result = metadata := receipt.logic

theorem every_scenario_has_valid_metadata (scenario : Scenario Model) :
    scenario.metadata.value.valid = true := scenario.metadata.valid

theorem create_preserves_model (metadata : Metadata) (model : Model) (scenario : Scenario Model)
    (created : create metadata model = .ok scenario) :
    scenario.metadata.value = metadata ∧ scenario.model = model := by
  unfold create at created
  split at created
  · cases created; exact ⟨rfl, rfl⟩
  · cases created

theorem derivation_retains_parent (parent : Scenario Parent) (metadata : Metadata)
    (bind : Parent → Model) (child : Scenario Model)
    (derived : derive parent metadata bind = .ok child) :
    child.ancestors = parent.metadata.value :: parent.ancestors := by
  unfold derive at derived
  split at derived
  · cases derived
  · cases created : create metadata (bind parent.model) with
    | error error => simp [created] at derived
    | ok result => simp [created] at derived; cases derived; rfl

theorem derivation_preserves_binding (parent : Scenario Parent) (metadata : Metadata)
    (bind : Parent → Model) (child : Scenario Model)
    (derived : derive parent metadata bind = .ok child) : child.model = bind parent.model := by
  unfold derive at derived
  split at derived
  · cases derived
  · cases created : create metadata (bind parent.model) with
    | error error => simp [created] at derived
    | ok result =>
      simp [created] at derived
      cases derived
      exact (create_preserves_model metadata (bind parent.model) result created).2

def Scenario.provenanceJson (scenario : Scenario Model) : Lean.Json := Lean.Json.mkObj [
  ("format_version", Lean.toJson (1 : Nat)),
  ("metadata", scenario.metadata.value.toJson),
  ("ancestors", Lean.toJson (scenario.ancestors.map Metadata.toJson))]

end CedarPooSpec.Scenarios
