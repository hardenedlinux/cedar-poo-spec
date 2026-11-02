import Init

/-! Generic typed predicates and immutable observations. No application imports. -/
namespace CedarPooSpec.ZeroTrust

abbrev Requirement (Effect View : Type) := Effect → View → Prop

/-- The application supplies meanings, not caller-controlled truth flags.
Each predicate is a separate refinement obligation at the actual effect use. -/
structure Framework (Effect View : Type) where
  authenticated : View → Prop
  authorized : Requirement Effect View
  currentAtUse : View → Prop
  consumptionCommitted : Requirement Effect View
  unknownRetained : Requirement Effect View
  revoked : Requirement Effect View
  mediated : Requirement Effect View

/-- Attribute values and a non-reused authoritative generation. Restoring an
equal value does not make an observation from an older generation current. -/
structure Observation (Attributes : Type) where
  generation : Nat
  attributes : Attributes
  deriving DecidableEq


end CedarPooSpec.ZeroTrust
