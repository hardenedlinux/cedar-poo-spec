import Lean
import CedarPooSpec.ZeroTrust

/-! Inspect the actual transitive import header, not a source substring.
This gate also catches a future intermediate module importing Gateway. -/
run_cmd do
  let environment ← Lean.getEnv
  for name in environment.header.moduleNames do
    if name.toString.startsWith "CedarPooSpec.Gateway" then
      throwError "functional Zero Trust core imported application module {name}"
