import CedarPooSpec.Gateway.OAuthReceiver

namespace Tests.Gateway.RecoveryPlan

inductive Worker where
  | a
  | b
  deriving DecidableEq

def Worker.name : Worker → String
  | .a => "a"
  | .b => "b"

def Worker.other : Worker → Worker
  | .a => .b
  | .b => .a

structure Step where
  event : String
  worker : String
  writerAdvance : Nat
  receiverAdvance : Nat
  originalStatus : String := "reconciled"
  missingStatus : String := "unresolved"
  storedReceipt : String := "original"
  receiverReceipt : String := "original"
  intentBound : Bool := true
  missingIntentBound : Bool := true
  revocationPreserved : Bool := true
  originalIdempotent : Bool := true
  conflictRefused : Bool := true
  missingPreserved : Bool := true
  oldWriterFenced : Bool := true
  oldReplicaFenced : Bool := true
  noResend : Bool := true
  mappingAccepted : Bool := true
  crossOperationRefused : Bool := true
  crossAuthorityRefused : Bool := true
  foreignProviderRefused : Bool := true
  foreignWitnessRefused : Bool := true
  sourceSubstitutionRefused : Bool := true
  intentSubstitutionRefused : Bool := true
  deriving DecidableEq

structure Round where
  firstWorker : Worker
  handoffsAfterFirst : Nat
  handoffsAfterSecond : Nat
  handoffsAfterConfirmation : Nat
  deriving DecidableEq

def Round.advances (round : Round) : Nat :=
  round.handoffsAfterFirst + round.handoffsAfterSecond + round.handoffsAfterConfirmation

def rounds : List Round := [⟨.a, 2, 2, 2⟩, ⟨.b, 4, 2, 2⟩, ⟨.a, 2, 4, 4⟩]

private def expected (event worker : String) (advance : Nat) : Step :=
  { event, worker, writerAdvance := advance, receiverAdvance := advance }

private def handoffs (start count : Nat) : List Step :=
  (List.range count).map fun index => expected "handoff" "authority" (start + index + 1)

def Round.steps (round : Round) : List Step :=
  let first := round.handoffsAfterFirst
  let second := first + round.handoffsAfterSecond
  [expected "ready" "both" 0, expected "worker-crash" round.firstWorker.name 0] ++
    handoffs 0 first ++
    [expected "fenced" round.firstWorker.other.name first,
     expected "worker-crash" round.firstWorker.other.name first] ++
    handoffs first round.handoffsAfterSecond ++
    [expected "confirmed" "both" second,
     expected "confirmation-lost" round.firstWorker.name second] ++
    handoffs second round.handoffsAfterConfirmation ++
    [expected "recovered" "both" round.advances]

def Step.toJson (step : Step) : Lean.Json := Lean.Json.mkObj [
  ("event", Lean.toJson step.event), ("worker", Lean.toJson step.worker),
  ("writer_advance", Lean.toJson step.writerAdvance), ("receiver_advance", Lean.toJson step.receiverAdvance),
  ("original_status", Lean.toJson step.originalStatus), ("missing_status", Lean.toJson step.missingStatus),
  ("stored_receipt", Lean.toJson step.storedReceipt), ("receiver_receipt", Lean.toJson step.receiverReceipt),
  ("intent_bound", Lean.toJson step.intentBound), ("missing_intent_bound", Lean.toJson step.missingIntentBound),
  ("revocation_preserved", Lean.toJson step.revocationPreserved), ("original_idempotent", Lean.toJson step.originalIdempotent),
  ("conflict_refused", Lean.toJson step.conflictRefused), ("missing_preserved", Lean.toJson step.missingPreserved),
  ("old_writer_fenced", Lean.toJson step.oldWriterFenced), ("old_replica_fenced", Lean.toJson step.oldReplicaFenced),
  ("no_resend", Lean.toJson step.noResend),
  ("mapping_accepted", Lean.toJson step.mappingAccepted),
  ("cross_operation_refused", Lean.toJson step.crossOperationRefused),
  ("cross_authority_refused", Lean.toJson step.crossAuthorityRefused),
  ("foreign_provider_refused", Lean.toJson step.foreignProviderRefused),
  ("foreign_witness_refused", Lean.toJson step.foreignWitnessRefused),
  ("source_substitution_refused", Lean.toJson step.sourceSubstitutionRefused),
  ("intent_substitution_refused", Lean.toJson step.intentSubstitutionRefused)]

def Round.toJson (round : Round) : Lean.Json := Lean.Json.mkObj [
  ("first_worker", Lean.toJson round.firstWorker.name),
  ("handoffs_after_first", Lean.toJson round.handoffsAfterFirst),
  ("handoffs_after_second", Lean.toJson round.handoffsAfterSecond),
  ("handoffs_after_confirmation", Lean.toJson round.handoffsAfterConfirmation),
  ("expected_advances", Lean.toJson round.advances),
  ("expected_crashes", Lean.toJson (3 : Nat)),
  ("steps", Lean.Json.arr (round.steps.map Step.toJson).toArray)]

def fixture : Lean.Json := Lean.Json.mkObj [
  ("format", Lean.toJson "cedar-poo-legacy-recovery-plan-v3"),
  ("scope", Lean.toJson "settled-read-only-recovery"),
  ("identity_mapping", Lean.toJson "operation-authority-provider-and-exact-signed-sources"),
  ("rounds", Lean.Json.arr (rounds.map Round.toJson).toArray)]

end Tests.Gateway.RecoveryPlan
