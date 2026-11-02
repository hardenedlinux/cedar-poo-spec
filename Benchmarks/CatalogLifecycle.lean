import CedarPooSpec.Transport.SourceCatalog

/-! Native lifecycle algorithms depend on typed producers, not a domain catalog.
They compile alongside the catalog; the executable supplies the same complete input. -/
namespace CedarPooSpec.CatalogLifecycleBenchmark

/-- The actual typed catalog, with one warmup and three fixed native samples.
Preparation and serialization stay inside their IO clock boundaries. -/
@[noinline] private def prepareActual (entries : List (String × CedarPooSpec.Transport.EntryProducer)) :
    IO CedarPooSpec.Transport.EncodedJson :=
  IO.ofExcept (CedarPooSpec.Transport.prepareCatalogFrom entries)

@[noinline] private def renderActual (encoded : CedarPooSpec.Transport.EncodedJson) : IO String :=
  pure encoded.wire

def benchmark (catalog : List (String × CedarPooSpec.Transport.EntryProducer)) : IO Unit := do
  let reference ← renderActual (← prepareActual catalog)
  let stdout ← IO.getStdout
  for sample in [1, 2, 3] do
    let started ← IO.monoNanosNow
    let encoded ← prepareActual catalog
    let prepared ← IO.monoNanosNow
    let wire ← renderActual encoded
    let finished ← IO.monoNanosNow
    unless wire == reference do
      throw (IO.userError "complete native catalog changed across samples")
    stdout.putStrLn s!"measurement: cedar.catalog.sample{sample}.prepare {prepared - started} ns"
    stdout.putStrLn s!"measurement: cedar.catalog.sample{sample}.serialize {finished - prepared} ns"
    stdout.putStrLn s!"measurement: cedar.catalog.sample{sample}.total {finished - started} ns"
  stdout.putStrLn s!"CATALOG-NATIVE-OK entries={catalog.length} bytes={reference.utf8ByteSize} checksum={hash reference} warmup=1 samples=3"

-- Use the exact production publication step and retained cross-entry source pools.
-- This attribution mode keeps the ordinary nine-measurement benchmark unchanged.
@[noinline] private def produceActualEntry (producer : CedarPooSpec.Transport.EntryProducer) :
    IO CedarPooSpec.Transport.Entry :=
  IO.ofExcept producer.run

@[noinline] private def publishActualEntry (entry : CedarPooSpec.Transport.Entry)
    (pools : CedarPooSpec.Transport.SourcePools) :
    IO (CedarPooSpec.Transport.EncodedJson × CedarPooSpec.Transport.SourcePools) := do
  let (encoded, next) ← IO.ofExcept ((entry.prepare).run pools)
  return (encoded.compact, next)

@[noinline] private def finishActualEntries (entries : List (String × CedarPooSpec.Transport.EncodedJson))
    (pools : CedarPooSpec.Transport.SourcePools) : IO CedarPooSpec.Transport.EncodedJson :=
  pure (pools.finish entries)

-- Diagnostic intervention only: force the existing, proof-bound response thunks
-- before the unmodified publisher. It still sees the same Cases and source pools.
@[noinline] private def forceCaseResponse (row : CedarPooSpec.Transport.Case) : IO Nat := do
  let response := row.response.get
  return (match response.decision with | .allow => 1 | .deny => 0) +
    response.determiningPolicies.toList.length + response.erroringPolicies.toList.length

private def forceManifestResponses (manifest : CedarPooSpec.Transport.Manifest) : IO (Nat × Nat) := do
  let mut rows := 0
  let mut checksum := 0
  for row in manifest.cases do
    checksum := checksum + (← forceCaseResponse row)
    rows := rows + 1
  return (rows, checksum)

private def forceEntryResponses : CedarPooSpec.Transport.Entry → IO (Nat × Nat)
  | .manifest value => forceManifestResponses value
  | .evolution before after => do
      let (first, left) ← forceManifestResponses before
      let (second, right) ← forceManifestResponses after
      return (first + second, left + right)
  | _ => pure (0, 0)

private def attributeActual (catalog : List (String × CedarPooSpec.Transport.EntryProducer)) (label : String) (separateAuthorization : Bool := false) : IO String := do
  let mut pools : CedarPooSpec.Transport.SourcePools := {}
  let mut entries := #[]
  let mut observations : Array (String × Nat × Nat × Nat × Nat) := #[]
  let mut authObservations : Array (String × Nat × Nat × Nat × Nat) := #[]
  for (name, producer) in catalog do
    let begin ← IO.monoNanosNow
    let firstAlloc ← IO.getNumHeartbeats
    let entry ← produceActualEntry producer
    let producedAlloc ← IO.getNumHeartbeats
    let produced ← IO.monoNanosNow
    if separateAuthorization then
      let begin ← IO.monoNanosNow
      let before ← IO.getNumHeartbeats
      let (rows, checksum) ← forceEntryResponses entry
      let after ← IO.getNumHeartbeats
      let authFinished ← IO.monoNanosNow
      authObservations := authObservations.push (name, authFinished-begin, after-before, rows, checksum)
    let publishBegin ← IO.monoNanosNow
    let publishAlloc ← IO.getNumHeartbeats
    let (encoded, next) ← publishActualEntry entry pools
    let publishedAlloc ← IO.getNumHeartbeats
    let published ← IO.monoNanosNow
    pools := next
    entries := entries.push (name, encoded)
    observations := observations.push (name, produced-begin, published-publishBegin,
      producedAlloc-firstAlloc, publishedAlloc-publishAlloc)
  let begin ← IO.monoNanosNow
  let firstAlloc ← IO.getNumHeartbeats
  let encoded ← finishActualEntries entries.toList pools
  let finishedAlloc ← IO.getNumHeartbeats
  let finished ← IO.monoNanosNow
  let wire ← renderActual encoded
  let renderedAlloc ← IO.getNumHeartbeats
  let rendered ← IO.monoNanosNow
  let stdout ← IO.getStdout
  for (name, elapsed, allocations, rows, checksum) in authObservations do
    stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.{name}.authorize {elapsed} ns"
    stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.{name}.authorize.small_allocations {allocations} count"
    stdout.putStrLn s!"AUTHORIZATION-STAGE entry={name} rows={rows} checksum={checksum}"
  for (name, produce, publish, produceAlloc, publishAlloc) in observations do
    stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.{name}.produce {produce} ns"
    stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.{name}.publish {publish} ns"
    stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.{name}.produce.small_allocations {produceAlloc} count"
    stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.{name}.publish.small_allocations {publishAlloc} count"
  stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.finish {finished-begin} ns"
  stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.serialize {rendered-finished} ns"
  stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.finish.small_allocations {finishedAlloc-firstAlloc} count"
  stdout.putStrLn s!"measurement: cedar.catalog.stages.{label}.serialize.small_allocations {renderedAlloc-finishedAlloc} count"
  return wire

def stageBenchmark (catalog : List (String × CedarPooSpec.Transport.EntryProducer)) (separateAuthorization : Bool := false) : IO Unit := do
  -- The first-use pass is separately visible, after native import initialization.
  let first ← attributeActual catalog "first-use" separateAuthorization
  for sample in [1, 2, 3] do
    let wire ← attributeActual catalog s!"sample{sample}" separateAuthorization
    unless wire == first do throw (IO.userError "stage catalog changed across samples")
  let reference ← renderActual (← prepareActual catalog)
  unless first == reference do throw (IO.userError "attribution changed production catalog")
  (← IO.getStdout).putStrLn s!"CATALOG-STAGES-OK entries={catalog.length} bytes={reference.utf8ByteSize} checksum={hash reference} first_use=1 samples=3 production_wire_equal=true"


end CedarPooSpec.CatalogLifecycleBenchmark
