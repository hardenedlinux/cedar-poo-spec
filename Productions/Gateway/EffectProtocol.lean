import CedarPooSpec.Gateway.EffectProtocol
import Lean.Data.Json

/-! Shared Production oracle for all schema-qualified vertical consumers.
No domain-specific policy or example/test module is imported. The catalogue
consumer supplies real Lean/Cedar decisions independently replayed by Rust. -/
namespace CedarPooSpec.Production.EffectProtocol
open Gateway.EffectProtocol CedarPooSpec.ZeroTrust

inductive Fault where
  | none | version | issuer | subject | audience | source | value | factGeneration
  | claimed | unverified | expired | missingFact | duplicateFact | extraFact
  | review | policy | schema | sourceRevision | epoch | resource | resourceGeneration
  | payload | actionSchema | effectAudience | observing | unmapped | revoked
  | unregistered | unconsumed | unknown | logFailure | crashAfterSend
  deriving DecidableEq, BEq, Repr

def faults : List Fault := [.none, .version, .issuer, .subject, .audience, .source,
  .value, .factGeneration, .claimed, .unverified, .expired, .missingFact,
  .duplicateFact, .extraFact, .review, .policy, .schema, .sourceRevision, .epoch,
  .resource, .resourceGeneration, .payload, .actionSchema, .effectAudience,
  .observing, .unmapped, .revoked, .unregistered, .unconsumed, .unknown,
  .logFailure, .crashAfterSend]

def baseFact : FactBinding String String :=
  ⟨"source-authority", "subject", "gateway", "current-world", "world", "digest", 7,
    .attested, 1, 100⟩

def baseEffect : EffectIdentity := ⟨"operation", "resource", 7, "payload", "schema", "gateway"⟩
def baseReview : ReviewBinding := ⟨"before", "after", "schema", "source", 7, "report"⟩
def baseEnvelope : Envelope := ⟨⟨1, 0⟩, baseEffect, baseReview, [baseFact]⟩
def baseCurrent : Current :=
  ⟨baseEffect, baseReview, ⟨fun _ => baseFact, fun _ => true, 10⟩,
    ["world"], true, true, false, true, true, false⟩

/-- Mutations are explicit protocol controls, not alternate industry decisions. -/
def mutate (fault : Fault) : Current × Envelope :=
  let fact := baseFact
  let current := baseCurrent
  let envelope := baseEnvelope
  match fault with
  | .none | .logFailure | .crashAfterSend => (current, envelope)
  | .version => (current, { envelope with version := ⟨2, 0⟩ })
  | .issuer => (current, { envelope with facts := [{fact with issuer := "other"}] })
  | .subject => (current, { envelope with facts := [{fact with subject := "other"}] })
  | .audience => (current, { envelope with facts := [{fact with audience := "other"}] })
  | .source => (current, { envelope with facts := [{fact with source := "other"}] })
  | .value => (current, { envelope with facts := [{fact with value := "other"}] })
  | .factGeneration => (current, { envelope with facts := [{fact with generation := 8}] })
  | .claimed => (current, { envelope with facts := [{fact with origin := .claimed}] })
  | .unverified => ({current with authority := {current.authority with verified := fun _ => false}}, envelope)
  | .expired => ({current with authority := {current.authority with now := 100}}, envelope)
  | .missingFact => (current, {envelope with facts := []})
  | .duplicateFact => (current, {envelope with facts := [fact, fact]})
  | .extraFact => (current, {envelope with facts := [fact, {fact with field := "extra"}]})
  | .review => (current, {envelope with review := {envelope.review with report := "other"}})
  | .policy => (current, {envelope with review := {envelope.review with after := "other"}})
  | .schema => (current, {envelope with review := {envelope.review with schema := "other"}})
  | .sourceRevision => (current, {envelope with review := {envelope.review with source := "other"}})
  | .epoch => (current, {envelope with review := {envelope.review with epoch := 8}})
  | .resource => (current, {envelope with effect := {envelope.effect with object := "other"}})
  | .resourceGeneration => (current, {envelope with effect := {envelope.effect with generation := 8}})
  | .payload => (current, {envelope with effect := {envelope.effect with payload := "other"}})
  | .actionSchema => (current, {envelope with effect := {envelope.effect with actionSchema := "other"}})
  | .effectAudience => (current, {envelope with effect := {envelope.effect with audience := "other"}})
  | .observing => ({current with enforcing := false}, envelope)
  | .unmapped => ({current with mapped := false}, envelope)
  | .revoked => ({current with revoked := true}, envelope)
  | .unregistered => ({current with registered := false}, envelope)
  | .unconsumed => ({current with consumed := false}, envelope)
  | .unknown => ({current with unknown := true}, envelope)


def simulate (fault : Fault) (cedarAllowed : Bool) : Outcome :=
  let (current, envelope) := mutate fault
  Outcome.resolve (accepts current envelope cedarAllowed)
    (fault != .logFailure) (fault == .crashAfterSend)


private def auditReportJson (report : AuditReport) : Lean.Json := Lean.Json.mkObj [
  ("unresolved_precommits", Lean.toJson report.unresolvedPrecommits),
  ("missing_receipts", Lean.toJson report.missingReceipts), ("missing_actions", Lean.toJson report.missingActions),
  ("mismatched", Lean.toJson report.mismatched), ("duplicates", Lean.toJson report.duplicates),
  ("invalid_receipts", Lean.toJson report.invalidReceipts), ("invalid_log", Lean.toJson report.invalidLog)]

def auditCases : List (String × List AuditRecord × List AuditRecord × Nat × Bool) :=
  let original : AuditRecord := ⟨"operation", "original"⟩
  [("clean", [original], [original], 0, true),
   ("precommitOnly", [], [], 0, true),
   ("missingReceipt", [original], [], 0, true), ("missingAction", [], [original], 0, true),
   ("mismatch", [{original with value := "changed"}], [original], 0, true),
   ("duplicateAction", [original,original], [original], 0, true),
   ("duplicateReceipt", [original], [original,original], 0, true),
   ("invalidReceipt", [original], [], 1, true),
   ("unanchoredReceipt", [original], [], 1, true),
   ("rewrittenLog", [original], [], 1, false),
   ("truncatedLog", [original], [], 1, false)]

private def outcomeJson (outcome : Outcome) : Lean.Json := Lean.Json.mkObj [
  ("admitted", Lean.toJson outcome.admitted), ("precommitted", Lean.toJson outcome.precommitted),
  ("sent", Lean.toJson outcome.sent), ("receipted", Lean.toJson outcome.receipted),
  ("unknown", Lean.toJson outcome.unknown)]

def fixture : Lean.Json := Lean.Json.mkObj [
  ("format_version", Lean.toJson (1 : Nat)),
  ("protocol", Lean.Json.mkObj [("major", Lean.toJson (1 : Nat)), ("minor", Lean.toJson (0 : Nat))]),
  ("audit_cases", Lean.toJson (auditCases.map fun (fault, actions, receipts, invalid, logValid) =>
    Lean.Json.mkObj [("fault", Lean.toJson fault),
      ("expected", auditReportJson (reconcile actions receipts invalid logValid
        (if logValid && fault != "unanchoredReceipt" then ["operation"] else [])))])),
  ("cases", Lean.toJson ([false, true].flatMap fun allowed => faults.map fun fault =>
    Lean.Json.mkObj [("fault", Lean.toJson ((reprStr fault).splitOn ".").getLast!),
      ("cedar_allowed", Lean.toJson allowed), ("expected", outcomeJson (simulate fault allowed))]))]
end CedarPooSpec.Production.EffectProtocol
