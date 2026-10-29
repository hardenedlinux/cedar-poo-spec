import CedarPooSpec.Data.Lakehouse.LocationBoundary
import LeanPoo.Object.Definition
import CedarPooSpec.Functional.ObjectProfile

/-! A typed location-boundary prototype. Descendants replace only selected
fields; the inherited boundary slot reads the final object. -/

namespace CedarPooSpec.Data.Lakehouse.LocationProfile

open Cedar.Spec LeanPoo

inductive Key where
  | template
  | policyId
  | actionScope
  | location
  | denyMissing
  | boundary
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .template => LocationBoundary
  | .policyId => PolicyID
  | .actionScope => ActionScope
  | .location => String
  | .denyMissing => Bool
  | .boundary => LocationBoundary

abbrev Object := LeanPoo.Object.Memoized Key Value

def define (name : String) (initial : LocationBoundary) :
    Except C4.Error Object :=
  LeanPoo.Object.define name do
    LeanPoo.Object.Declaration.Builder.value .template initial
    LeanPoo.Object.Declaration.Builder.value .policyId initial.policyId
    LeanPoo.Object.Declaration.Builder.value .actionScope initial.actionScope
    LeanPoo.Object.Declaration.Builder.value .location initial.deniedLocation
    LeanPoo.Object.Declaration.Builder.value .denyMissing initial.denyMissing
    LeanPoo.Object.Declaration.Builder.slot .boundary
      (.self fun self => do
        let policyId ← self .policyId
        let actionScope ← self .actionScope
        let deniedLocation ← self .location
        let denyMissing ← self .denyMissing
        pure { initial with policyId, actionScope, deniedLocation, denyMissing })

open LeanPoo.Functional.ObjectContract

def contract : Contract Object Key Unit String :=
  refine (Functional.ObjectProfile.shape [.template, .policyId, .actionScope, .location, .denyMissing, .boundary]) fun profile path =>
    match profile.read .template, profile.read .policyId, profile.read .actionScope,
        profile.read .location, profile.read .denyMissing, profile.read .boundary with
    | some template, some policyId, some actionScope, some deniedLocation, some denyMissing, some boundary =>
      if boundary = { template with policyId, actionScope, deniedLocation, denyMissing } then []
      else [.rejected path "location projection mismatch"]
    | _, _, _, _, _, _ => [.rejected path "missing location projection"]

def issues (profile : Object) := diagnose contract profile []

def boundary? (profile : Object) : Option LocationBoundary :=
  Functional.ObjectProfile.read contract profile .boundary

theorem boundary_requires_contract (profile : Object) (value : LocationBoundary)
    (accepted : boundary? profile = some value) : diagnose contract profile [] = [] :=
  Functional.ObjectProfile.read_requires_contract contract profile _ _ accepted

end CedarPooSpec.Data.Lakehouse.LocationProfile
