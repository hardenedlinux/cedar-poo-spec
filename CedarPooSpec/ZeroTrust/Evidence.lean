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


/-- A typed projection of one signed source statement. The verifier is supplied
by the independently configured Host, never decoded from an input truth flag. -/
structure FactStatement (Field Value : Type) where
  issuer : String
  major : Nat := 1
  minor : Nat := 0
  facts : List (FactBinding Field Value)

def FactStatement.valid (statement : FactStatement Field Value)
    (verified : FactStatement Field Value → Bool) : Bool :=
  decide (statement.major = 1 ∧ statement.minor = 0 ∧ statement.facts ≠ []) &&
    verified statement && statement.facts.all (fun fact => decide (fact.issuer = statement.issuer))

def FactAuthority.acceptsStatements (authority : FactAuthority Field Value)
    (required : List Field) (statements : List (FactStatement Field Value))
    (verified : FactStatement Field Value → Bool) : Bool :=
  statements.all (fun statement => statement.valid verified) &&
    authority.acceptsAll required (statements.flatMap (·.facts))

theorem accepted_statements_preserve_field_admission (authority : FactAuthority Field Value)
    (required : List Field) (statements : List (FactStatement Field Value))
    (verified : FactStatement Field Value → Bool)
    (accepted : authority.acceptsStatements required statements verified = true) :
    authority.acceptsAll required (statements.flatMap (·.facts)) = true :=
  (Bool.and_eq_true_iff.mp accepted).2

theorem accepted_statements_are_verified (authority : FactAuthority Field Value)
    (required : List Field) (statements : List (FactStatement Field Value))
    (verified : FactStatement Field Value → Bool)
    (accepted : authority.acceptsStatements required statements verified = true)
    (statement : FactStatement Field Value) (member : statement ∈ statements) :
    verified statement = true ∧ ∀ fact ∈ statement.facts, fact.issuer = statement.issuer := by
  have valid := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp accepted).1) statement member
  have parts := Bool.and_eq_true_iff.mp valid
  exact ⟨(Bool.and_eq_true_iff.mp parts.1).2, by
    simpa using List.all_eq_true.mp parts.2⟩

theorem accepted_statements_cover_exact_inventory (authority : FactAuthority Field Value)
    (required : List Field) (statements : List (FactStatement Field Value))
    (verified : FactStatement Field Value → Bool)
    (accepted : authority.acceptsStatements required statements verified = true) :
    required ≠ [] ∧ required.Nodup ∧
      ((statements.flatMap (·.facts)).map (·.field)).Perm required ∧
      ∀ fact ∈ statements.flatMap (·.facts), authority.accepts fact = true :=
  accepted_inventory_covers_required authority required _
    (accepted_statements_preserve_field_admission authority required statements verified accepted)

end CedarPooSpec.ZeroTrust
