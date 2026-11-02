import CedarPooSpec.Gateway.ProfileObject

/-! Reuse the actual LeanPoo factory-indexed Session as the profile authority
payload. A Host chooses/authenticates the current publication independently of
the candidate; this pure library implements neither a registry nor signatures. -/
namespace CedarPooSpec.Gateway
open Cedar.Spec

namespace ProfileObject

structure Publication (original : Profile) (object : Object) where
  context : Context
  session : Session original object
  selected : Profile
  projected : session.read .profile = some selected

/-- The original and actual object are retained in the publication's type.
No caller-supplied profile name is used to look up or substitute its content. -/
def capturePublication (context : Context) (session : Session original object) :
    Except Error (Publication original object) :=
  match projected : session.read .profile with
  | none => .error .invalidProfile
  | some selected => .ok ⟨context, session, selected, projected⟩

theorem Publication.preserves_original (publication : Publication original object) :
    original.Refines publication.selected :=
  read_preserves_original_requirements publication.session publication.selected publication.projected

end ProfileObject

variable {E S : Type} {project : E → S → Request}
  {prepared : Prepared E S project} {model : PolicyModules.Model}
  {effect : E} {state : S} {actualContext : Context} {checks : List Assessment}
  {entities : Entities} {original : Profile} {object : ProfileObject.Object}

/-- Consumption requires this publication-indexed evidence, never a raw Receipt.
The Host must supply the actually authoritative publication at final use. -/
structure PublishedReceipt (publication : ProfileObject.Publication original object)
    (prepared : Prepared E S project) (model : PolicyModules.Model)
    (effect : E) (state : S) (actualContext : Context)
    (checks : List Assessment) (entities : Entities) where
  semantic : Receipt prepared model effect state actualContext checks entities
  profileBound : prepared.profile = publication.selected
  contextBound : actualContext = publication.context

private def requireBinding (condition : Prop) [Decidable condition] (error : Error) :
    Except Error (PLift condition) :=
  if evidence : condition then .ok ⟨evidence⟩ else .error error

def bindPublication (publication : ProfileObject.Publication original object)
    (receipt : Receipt prepared model effect state actualContext checks entities) :
    Except Error (PublishedReceipt publication prepared model effect state actualContext checks entities) := do
  let profile ← requireBinding (prepared.profile = publication.selected) .invalidProfile
  let context ← requireBinding (actualContext = publication.context) .staleContext
  return ⟨receipt, profile.down, context.down⟩

/-- Actual authority is supplied separately from the candidate. Rebinding runs
for raw and object-derived preparations alike; origin labels cannot skip it. -/
def authorizePublished [DecidableEq E] [DecidableEq S]
    (publication : ProfileObject.Publication original object)
    (prepared : Prepared E S project) (model : PolicyModules.Model)
    (effect : E) (state : S) (actualContext : Context)
    (checks : List Assessment) (entities : Entities) :
    Except Error (PublishedReceipt publication prepared model effect state actualContext checks entities) := do
  let receipt ← authorize prepared model effect state actualContext checks entities
  bindPublication publication receipt

variable {publication : ProfileObject.Publication original object}

theorem published_profile_refines_authoritative_original
    (receipt : PublishedReceipt publication prepared model effect state actualContext checks entities) :
    original.Refines prepared.profile := by
  rw [receipt.profileBound]
  exact publication.preserves_original

theorem published_scope_cannot_reset
    (receipt : PublishedReceipt publication prepared model effect state actualContext checks entities) :
    prepared.context.scope = publication.context.scope :=
  (admitted_original_scope_is_preserved receipt.semantic).trans
    (congrArg Context.scope receipt.contextBound)

theorem weakened_original_cannot_have_published_receipt
    (weakened : ¬ original.Refines prepared.profile) :
    ¬ Nonempty (PublishedReceipt publication prepared model effect state actualContext checks entities) :=
  fun ⟨receipt⟩ => weakened (published_profile_refines_authoritative_original receipt)

theorem published_original_obligations_are_satisfied
    (receipt : PublishedReceipt publication prepared model effect state actualContext checks entities) :
    ∀ name ∈ original.requiredChecks,
      ∃ assessment ∈ checks, assessment.name = name ∧ assessment.status = .satisfied := by
  apply ProfileObject.inherited_obligations_are_satisfied publication.session
    publication.selected publication.projected checks
  simpa only [← receipt.profileBound] using receipt.semantic.checksAccepted

theorem wrong_profile_cannot_bind
    (publication : ProfileObject.Publication original object)
    (receipt : Receipt prepared model effect state actualContext checks entities)
    (different : prepared.profile ≠ publication.selected) :
    bindPublication publication receipt = .error .invalidProfile := by
  simp [bindPublication, requireBinding, different]

theorem changed_context_cannot_bind
    (publication : ProfileObject.Publication original object)
    (different : actualContext ≠ publication.context) :
    ¬ Nonempty (PublishedReceipt publication prepared model effect state actualContext checks entities) :=
  fun ⟨bound⟩ => different bound.contextBound

end CedarPooSpec.Gateway
