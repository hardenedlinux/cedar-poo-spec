import CedarPooSpec.Gateway.OAuthReceiptBatch

namespace Tests.Gateway.SettledLatePlan
open CedarPooSpec.Gateway.OAuth

/-- Portable predicates, derived independently from Lean rows and native signed sources. -/
structure Step where
  event : String
  worker : String
  writerAdvance : Nat
  receipt : String
  operationBound : Bool
  authorityBound : Bool
  intentSourceBound : Bool
  outcomeSourceBound : Bool
  versionBound : Bool
  intentBound : Bool
  legacyDigestBound : Bool
  originalIdempotent : Bool
  conflictRefused : Bool
  oldWriterFenced : Bool
  oldReplicaFenced : Bool
  missingPreserved : Bool
  intentsPreserved : Bool
  revocationPreserved : Bool
  noResend : Bool
  deriving DecidableEq

private def expected (event worker : String) (advance : Nat) (bound : Bool) : Step :=
  { event, worker, writerAdvance := advance, receipt := if bound then "original" else "absent"
    operationBound := bound, authorityBound := bound, intentSourceBound := bound
    outcomeSourceBound := bound, versionBound := bound, intentBound := true
    legacyDigestBound := true, originalIdempotent := bound, conflictRefused := true
    oldWriterFenced := true, oldReplicaFenced := true, missingPreserved := true
    intentsPreserved := true, revocationPreserved := true, noResend := true }

def steps : List Step :=
  [expected "ready" "both" 0 false] ++
  [expected "staged-crash" "a" 0 false, expected "handoff" "authority" 1 false,
   expected "fenced" "b" 1 false,
   expected "staged-crash" "b" 1 false, expected "handoff" "authority" 2 false,
   expected "fenced" "a" 2 false,
   expected "durable-crash" "a" 2 true, expected "confirmed" "b" 2 true] ++
  ((List.range 4).flatMap fun index =>
    let worker := if index % 2 = 0 then "a" else "b"
    let peer := if index % 2 = 0 then "b" else "a"
    [expected "handoff" "authority" (index + 3) true,
     expected "confirmation-lost" worker (index + 3) true,
     expected "confirmed" peer (index + 3) true]) ++
  [expected "recovered" "a" 6 true]

def observe (initial image : ReceiptRecovery.Image) (delayed : ReceiptRecovery.Input)
    (retry : Revocation.Crash.BeginInput) (event worker : String) : Step :=
  let request := delayed.request
  let operation := request.operation
  let row := ReceiptRecovery.lookup image.rows operation
  let identity := image.receiptIdentity operation
  let sources := image.receiptSources operation
  let original := { delayed with image, writer := image.oauth.writer, mode := .settled }
  let conflict := { original with request := { request with outcomeSource :=
    { request.outcomeSource with signature := [99] } } }
  let oldWriter := ReceiptBatch.State.step { image } { original with writer := image.oauth.writer - 1 }
  let oldReplica := ReceiptBatch.State.step { image }
    { original with recovery := { original.recovery with placement := "retired-replica" } }
  let intent := request.symbolic.receipt.commit
  let replay := { retry with
    image := image.oauth, operation, intent
    writer := image.oauth.writer, checkedWriter := image.oauth.writer }
  { event, worker, writerAdvance := image.oauth.writer - initial.oauth.writer
    receipt := match row with
      | none => "absent"
      | some actual => if actual.symbolic = request.symbolic then "original" else "conflict"
    operationBound := identity.any fun actual => actual.operation == request.identity.operation
    authorityBound := identity.any fun actual => decide
      (actual.receiver = request.identity.receiver ∧
       actual.providerKey = request.identity.providerKey ∧
       actual.witnessKey = request.identity.witnessKey)
    intentSourceBound := sources.any (fun actual => actual.1 == request.intentSource) &&
      identity.any (fun actual => actual.intentDigest == request.identity.intentDigest)
    outcomeSourceBound := sources.any (fun actual => actual.2 == request.outcomeSource) &&
      identity.any (fun actual => actual.outcomeDigest == request.identity.outcomeDigest)
    versionBound := identity.any fun actual => actual.version == request.identity.version
    intentBound := decide ((image.oauth.retained.find? fun entry => entry.intent.operation == operation).map
      (·.intent) = some intent)
    legacyDigestBound := image.outcomeDigest operation == some request.identity.outcomeDigest
    originalIdempotent := ReceiptRecovery.persist original == some image
    conflictRefused := (ReceiptRecovery.persist conflict).isNone
    oldWriterFenced := oldWriter.stopped == some operation
    oldReplicaFenced := oldReplica.stopped == some operation
    missingPreserved :=
      (ReceiptRecovery.lookup image.rows "unavailable-effect").isNone &&
      (ReceiptRecovery.lookup initial.rows "unavailable-effect").isNone
    intentsPreserved := decide (image.oauth.retained.map (·.intent) = initial.oauth.retained.map (·.intent))
    revocationPreserved := decide (image.oauth.oauth = initial.oauth.oauth)
    noResend := (Revocation.Crash.begin replay).isNone }

def Step.toJson (step : Step) : Lean.Json := Lean.Json.mkObj [
  ("event", Lean.toJson step.event), ("worker", Lean.toJson step.worker),
  ("writer_advance", Lean.toJson step.writerAdvance), ("receipt", Lean.toJson step.receipt),
  ("operation_bound", Lean.toJson step.operationBound),
  ("authority_bound", Lean.toJson step.authorityBound),
  ("intent_source_bound", Lean.toJson step.intentSourceBound),
  ("outcome_source_bound", Lean.toJson step.outcomeSourceBound),
  ("version_bound", Lean.toJson step.versionBound),
  ("intent_bound", Lean.toJson step.intentBound),
  ("legacy_digest_bound", Lean.toJson step.legacyDigestBound),
  ("original_idempotent", Lean.toJson step.originalIdempotent),
  ("conflict_refused", Lean.toJson step.conflictRefused),
  ("old_writer_fenced", Lean.toJson step.oldWriterFenced),
  ("old_replica_fenced", Lean.toJson step.oldReplicaFenced),
  ("missing_preserved", Lean.toJson step.missingPreserved),
  ("intents_preserved", Lean.toJson step.intentsPreserved),
  ("revocation_preserved", Lean.toJson step.revocationPreserved),
  ("no_resend", Lean.toJson step.noResend)]

def fixture : Lean.Json := Lean.Json.mkObj [
  ("format", Lean.toJson "cedar-poo-settled-late-plan-v1"),
  ("scope", Lean.toJson "late-settled-receipt-step-alignment"),
  ("identity_mapping", Lean.toJson "operation-authority-version-and-exact-signed-sources"),
  ("steps", Lean.Json.arr (steps.map Step.toJson).toArray)]

end Tests.Gateway.SettledLatePlan
