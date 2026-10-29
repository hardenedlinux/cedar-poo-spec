import CedarPooSpec.Data.ProtectedStorage
import LeanPoo.Object.Definition
import CedarPooSpec.Functional.ObjectProfile

/-!
LeanPoo-owned composition for protected storage profiles. The public wire
contract remains `ProtectionIntent`; this object family owns configuration
inheritance and recomputes the final intent when a child overrides a slot.
-/

namespace CedarPooSpec.Data.ProtectionProfile

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

abbrev Object := LeanPoo.Object.Memoized Key Value

def define (name : String) (intent : ProtectionIntent) :
    Except C4.Error Object :=
  LeanPoo.Object.define name do
    LeanPoo.Object.Declaration.Builder.value .storage intent.storage
    LeanPoo.Object.Declaration.Builder.value .profile intent.profile
    LeanPoo.Object.Declaration.Builder.value .keyRef intent.keyRef
    LeanPoo.Object.Declaration.Builder.value .keyVersion intent.keyVersion
    LeanPoo.Object.Declaration.Builder.value .residency intent.residency
    LeanPoo.Object.Declaration.Builder.slot .intent
      (.self fun self => do
        let storage ← self .storage
        let profile ← self .profile
        let keyRef ← self .keyRef
        let keyVersion ← self .keyVersion
        let residency ← self .residency
        pure { storage, profile, keyRef, keyVersion, residency })

def withStorage (parent : Object) (name : String) (storage : StorageEffect) :
    Except C4.Error Object :=
  parent.extendWith name do
    LeanPoo.Object.Declaration.Builder.value .storage storage

def withKeyVersion (parent : Object) (name keyVersion : String) :
    Except C4.Error Object :=
  parent.extendWith name do
    LeanPoo.Object.Declaration.Builder.value .keyVersion keyVersion

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
