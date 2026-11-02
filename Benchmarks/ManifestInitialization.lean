import Init.System.IO

namespace CedarPooSpec.ManifestInitialization

/-- First diagnostic import: brackets subsequent native module initialization.
    Loader/runtime work before this module is deliberately outside this span. -/
initialize started : Nat ← IO.monoNanosNow

end CedarPooSpec.ManifestInitialization
