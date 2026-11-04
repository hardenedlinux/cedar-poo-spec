import Init.System.IO

namespace CedarPooSpec.ReviewedEffectCatalog

/- Pinned Lean 4.35 runtime ABI: these are the exact exported C functions and
   argument types used by Lean/Shell.lean for -M and -T. The Shell's Lean
   declarations are private, so this application-owned adapter imports only
   their runtime budget ABI rather than the compiler/frontend. -/
@[extern "lean_internal_set_max_memory"]
private opaque setProducerMaxMemory (bytes : USize) : BaseIO Unit
@[extern "lean_internal_set_max_heartbeat"]
private opaque setProducerMaxHeartbeat (heartbeats : USize) : BaseIO Unit

/-- First producer import: retain -M 2048 and -T 10000000 before manifest
initialization. The unchanged process watchdog is applied by the caller. -/
initialize reviewedProducerLimits : Unit ← do
  setProducerMaxMemory (2048 * 1024 * 1024)
  setProducerMaxHeartbeat (10000000 * 1000)

end CedarPooSpec.ReviewedEffectCatalog
