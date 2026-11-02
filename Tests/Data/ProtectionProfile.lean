import CedarPooSpec.Data.ProtectionProfile
import Productions.Data.ProtectedStorageFixture

namespace CedarPooSpec.Data.ProtectionProfileTests

open CedarPooSpec.Data CedarPooSpec.Data.ProtectionProfile
open CedarPooSpec.Data.ProtectedStorageFixture

private def revisedIntent? : Option ProtectionIntent :=
  (ProtectionProfile.define "base" baseIntent).toOption.bind fun parent =>
    (ProtectionProfile.withKeyVersion parent "rotated" "key-version-8").toOption.bind
      ProtectionProfile.intent?

private def originalIntent? : Option ProtectionIntent :=
  (ProtectionProfile.define "base" baseIntent).toOption.bind ProtectionProfile.intent?

theorem inheritedIntentRecomputesKeyVersion :
    revisedIntent?.map (·.keyVersion) = some "key-version-8" := by
  native_decide

theorem parentRetainsOriginalVersion :
    originalIntent?.map (·.keyVersion) = some "key-version-7" := by
  native_decide

theorem revisionRetainsCustodyAndSource :
    revisedIntent?.map (·.storage) = some baseIntent.storage := by
  native_decide

end CedarPooSpec.Data.ProtectionProfileTests
