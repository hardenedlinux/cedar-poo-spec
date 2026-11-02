import Productions.Data.StorageEffectFixture
import Productions.Data.ProtectedStorageFixture
import CedarPooSpec.Data.ProtectionProfile
import Lean.Data.Json

/-!
Cross-profile production matrix. Each case is one exact physical effect
evaluated as raw storage and as protected storage under the same current
governance. Rust replays the checked JSON; the Host still authenticates its
inputs and enforces the selected path.
-/

namespace CedarPooSpec.Data.StorageProfileMatrix

open CedarPooSpec.Data Lean

private def obj (fields : List (String × Json)) : Json := Json.mkObj fields

def cases : List (String × StorageEffect × CurrentStorageState) := Id.run do
  let mut result := []
  for restricted in [false, true] do
    for acceptsRestricted in [false, true] do
      for tenantMatches in [false, true] do
        for tier in [StorageTier.durableLocal, StorageTier.remote] do
          let effect := { StorageEffectFixture.baseEffect with
            sources := [{ StorageEffectFixture.baseSource with
              restricted, tenant := if tenantMatches then "tenant-a" else "tenant-b" }],
            destination := { StorageEffectFixture.baseDestination with acceptsRestricted },
            tier }
          let name := s!"restricted={restricted};accepts={acceptsRestricted};" ++
            s!"tenant={tenantMatches};tier={if tier == .remote then "remote" else "local"}"
          result := result ++ [(name, effect, StorageEffectFixture.baseCurrent)]
  return result

def rawAllowed (effect : StorageEffect) (current : CurrentStorageState) : Bool :=
  effect.rawAdmitted { effect, epoch := 4, expiresAt := 100, allowed := true } current

def protectedDecision? (effect : StorageEffect)
    (current : CurrentStorageState) : Option Bool :=
  (ProtectionProfile.define "matrix-base" ProtectedStorageFixture.baseIntent).toOption.bind fun base =>
    (ProtectionProfile.withStorage base "matrix-case" effect).toOption.bind fun variant =>
      (ProtectionProfile.intent? variant).map fun intent =>
        intent.admitted { intent, epoch := 4, expiresAt := 100, allowed := true } current

def protectedAllowed (effect : StorageEffect) (current : CurrentStorageState) : Bool :=
  (protectedDecision? effect current).getD false

def fixture : Json :=
  obj [("schema", toJson "cedar-poo-storage-profiles-v1"),
    ("cases", toJson (cases.map fun (name, effect, current) =>
      obj [("name", toJson name),
        ("effect", StorageEffectFixture.effectJson effect),
        ("current", StorageEffectFixture.currentJson current),
        ("protection", obj [("profile", toJson ProtectedStorageFixture.baseIntent.profile),
          ("key_ref", toJson ProtectedStorageFixture.baseIntent.keyRef),
          ("key_version", toJson ProtectedStorageFixture.baseIntent.keyVersion),
          ("residency", toJson ProtectedStorageFixture.baseIntent.residency)]),
        ("raw_allow", toJson (rawAllowed effect current)),
        ("profile_composed", toJson ((protectedDecision? effect current).isSome)),
        ("protected_allow", toJson (protectedAllowed effect current))]))]

end CedarPooSpec.Data.StorageProfileMatrix
