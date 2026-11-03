import CedarPooSpec.ZeroTrust.Composition

/-! Field evidence is checked against independent source policy and current
observations. The verifier is a Host interpretation, not an incoming truth flag.
A signature establishes an issuer's statement, not semantic truth. -/
namespace CedarPooSpec.ZeroTrust

inductive EvidenceOrigin where
  | claimed | observed | attested
  deriving DecidableEq, BEq, Repr

structure FactBinding (Field Value : Type) where
  issuer : String
  subject : String
  audience : String
  source : String
  field : Field
  value : Value
  generation : Nat
  origin : EvidenceOrigin
  notBefore : Nat
  expiresAt : Nat
  deriving DecidableEq

structure FactAuthority (Field Value : Type) where
  expected : Field → FactBinding Field Value
  verified : FactBinding Field Value → Bool
  now : Nat

variable [DecidableEq Field] [DecidableEq Value]

def FactAuthority.accepts (authority : FactAuthority Field Value)
    (evidence : FactBinding Field Value) : Bool :=
  decide (evidence = authority.expected evidence.field ∧
    evidence.origin ≠ .claimed ∧ evidence.notBefore ≤ authority.now ∧
    authority.now < evidence.expiresAt) && authority.verified evidence

theorem accepted_fact_is_current_and_verified (authority : FactAuthority Field Value)
    (evidence : FactBinding Field Value) (accepted : authority.accepts evidence = true) :
    evidence = authority.expected evidence.field ∧ evidence.origin ≠ .claimed ∧
    evidence.notBefore ≤ authority.now ∧ authority.now < evidence.expiresAt ∧
    authority.verified evidence = true := by
  simpa [FactAuthority.accepts, and_assoc] using accepted

theorem claimed_fact_is_refused (authority : FactAuthority Field Value)
    (evidence : FactBinding Field Value) (claimed : evidence.origin = .claimed) :
    authority.accepts evidence = false := by simp [FactAuthority.accepts, claimed]

theorem unverified_fact_is_refused (authority : FactAuthority Field Value)
    (evidence : FactBinding Field Value) (unverified : authority.verified evidence = false) :
    authority.accepts evidence = false := by simp [FactAuthority.accepts, unverified]

/-- All required fields must occur exactly once. Extra, duplicated and omitted
fields cannot be hidden by a successful check of one evidence item. -/
def FactAuthority.acceptsAll (authority : FactAuthority Field Value)
    (required : List Field) (evidence : List (FactBinding Field Value)) : Bool :=
  decide (required ≠ [] ∧ required.Nodup ∧ (evidence.map (·.field)).Perm required) &&
    evidence.all authority.accepts

theorem accepted_inventory_covers_required (authority : FactAuthority Field Value)
    (required : List Field) (evidence : List (FactBinding Field Value))
    (accepted : authority.acceptsAll required evidence = true) :
    required ≠ [] ∧ required.Nodup ∧ (evidence.map (·.field)).Perm required ∧
      ∀ fact ∈ evidence, authority.accepts fact = true := by
  simpa [FactAuthority.acceptsAll, List.all_eq_true, and_assoc] using accepted

end CedarPooSpec.ZeroTrust
