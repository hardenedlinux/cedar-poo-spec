import CedarPooSpec.Data.ProtectedStorage
import LeanPoo.Object.Dataflow
import CedarPooSpec.Functional.ObjectProfile

/-!
LeanPoo-owned composition for protected storage profiles. The public wire
contract remains `ProtectionIntent`; this object family owns configuration
inheritance and recomputes the final intent when a child overrides a slot.
-/

namespace CedarPooSpec.Data.ProtectionProfile
open LeanPoo.Object.Dataflow (Expr)

open CedarPooSpec.Data LeanPoo

inductive Key where
  | storage
  | profile
  | keyRef
  | keyVersion
  | residency
  | intent
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .storage => StorageEffect
  | .profile | .keyRef | .keyVersion | .residency => String
  | .intent => ProtectionIntent

abbrev Object := LeanPoo.Object.Dataflow.Instance Key Value

def define (name : String) (intent : ProtectionIntent) :
    Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  LeanPoo.Object.Dataflow.define name do
    LeanPoo.Object.Dataflow.Builder.value .storage intent.storage
    LeanPoo.Object.Dataflow.Builder.value .profile intent.profile
    LeanPoo.Object.Dataflow.Builder.value .keyRef intent.keyRef
    LeanPoo.Object.Dataflow.Builder.value .keyVersion intent.keyVersion
    LeanPoo.Object.Dataflow.Builder.value .residency intent.residency
    LeanPoo.Object.Dataflow.Builder.derived .intent
      ((fun storage profile keyRef keyVersion residency => { storage, profile, keyRef, keyVersion, residency })
        <$> Expr.need (Value := Value) .storage
        <*> Expr.need (Value := Value) .profile
        <*> Expr.need (Value := Value) .keyRef
        <*> Expr.need (Value := Value) .keyVersion
        <*> Expr.need (Value := Value) .residency)

def withStorage (parent : Object) (name : String) (storage : StorageEffect) :
    Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  parent.extendWith name do
    LeanPoo.Object.Dataflow.Builder.value .storage storage

def withKeyVersion (parent : Object) (name keyVersion : String) :
    Except (LeanPoo.Object.Dataflow.Error Key) Object :=
  parent.extendWith name do
    LeanPoo.Object.Dataflow.Builder.value .keyVersion keyVersion

open LeanPoo.Functional.ObjectContract

def contract : Contract Object Key Unit String :=
  refine (Functional.ObjectProfile.shape [.storage, .profile, .keyRef, .keyVersion, .residency, .intent])
    fun profile path =>
      match profile.read .storage, profile.read .profile, profile.read .keyRef,
          profile.read .keyVersion, profile.read .residency, profile.read .intent with
      | some storage, some selected, some keyRef, some keyVersion, some residency, some intent =>
        if !selected.isEmpty && !keyRef.isEmpty && !keyVersion.isEmpty && !residency.isEmpty &&
            decide (intent = { storage, profile := selected, keyRef, keyVersion, residency }) then []
        else [.rejected path "protection intent projection mismatch"]
      | _, _, _, _, _, _ => [.rejected path "missing protection intent projection"]

def issues (profile : Object) := diagnose contract profile []

def intent? (profile : Object) : Option ProtectionIntent :=
  Functional.ObjectProfile.read contract profile .intent

theorem intent_requires_contract (profile : Object) (intent : ProtectionIntent)
    (accepted : intent? profile = some intent) : diagnose contract profile [] = [] :=
  Functional.ObjectProfile.read_requires_contract contract profile _ _ accepted

end CedarPooSpec.Data.ProtectionProfile
