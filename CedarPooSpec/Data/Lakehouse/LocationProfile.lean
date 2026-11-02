import CedarPooSpec.Data.Lakehouse.LocationBoundary
import LeanPoo.Object.Dataflow
import CedarPooSpec.Functional.ObjectProfile

/-! A typed location-boundary prototype. Descendants replace only selected
fields; the inherited boundary slot reads the final object. -/

namespace CedarPooSpec.Data.Lakehouse.LocationProfile
open LeanPoo.Object.Dataflow (Expr)

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

abbrev Object := LeanPoo.Object.Dataflow.Instance Key Value

def define (name : String) (initial : LocationBoundary) :
    Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  LeanPoo.Object.Dataflow.define name do
    LeanPoo.Object.Dataflow.Builder.value .template initial
    LeanPoo.Object.Dataflow.Builder.value .policyId initial.policyId
    LeanPoo.Object.Dataflow.Builder.value .actionScope initial.actionScope
    LeanPoo.Object.Dataflow.Builder.value .location initial.deniedLocation
    LeanPoo.Object.Dataflow.Builder.value .denyMissing initial.denyMissing
    LeanPoo.Object.Dataflow.Builder.derived .boundary
      ((fun policyId actionScope deniedLocation denyMissing => { initial with policyId, actionScope, deniedLocation, denyMissing })
        <$> Expr.need (Value := Value) .policyId
        <*> Expr.need (Value := Value) .actionScope
        <*> Expr.need (Value := Value) .location
        <*> Expr.need (Value := Value) .denyMissing)

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
