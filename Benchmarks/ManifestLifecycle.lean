import Benchmarks.ManifestInitialization
import Benchmarks.CatalogLifecycle
import Examples.ManifestCatalog
import Std.Time.DateTime.Timestamp

/- Diagnostic entrypoint; the first import still brackets native initialization. -/

def main (args : List String) : IO Unit := do
  let started ← IO.monoNanosNow
  let entry ← Std.Time.Timestamp.now
  let pid ← IO.Process.getPID
  let stderr ← IO.getStderr
  stderr.putStrLn (Lean.Json.mkObj [
    ("observation", Lean.toJson "native-main-entry"), ("pid", Lean.toJson pid.toNat),
    ("import_initialization_ns", Lean.toJson (started - CedarPooSpec.ManifestInitialization.started)),
    ("unix_ns", Lean.toJson entry.toNanosecondsSinceUnixEpoch.toInt)]).compress
  if args == ["benchmark"] then CedarPooSpec.CatalogLifecycleBenchmark.benchmark CedarPooSpec.Manifests.entries
  else if args == ["stages"] then CedarPooSpec.CatalogLifecycleBenchmark.stageBenchmark CedarPooSpec.Manifests.entries
  else if args == ["stages-authorized"] then CedarPooSpec.CatalogLifecycleBenchmark.stageBenchmark CedarPooSpec.Manifests.entries true
  else CedarPooSpec.Manifests.run args true
  stderr.putStrLn (Lean.Json.mkObj [
    ("observation", Lean.toJson "native-main-return"), ("success", Lean.toJson true),
    ("unix_ns", Lean.toJson (← Std.Time.Timestamp.now).toNanosecondsSinceUnixEpoch.toInt),
    ("elapsed_ns", Lean.toJson ((← IO.monoNanosNow) - started))]).compress
