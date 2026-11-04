import CedarPooSpec.Gateway.Lifecycle
import Productions.Gateway.EffectProtocol

namespace CedarPooSpec.Production.Lifecycle
open Gateway.EffectProtocol Gateway.Lifecycle

def seed (cedarAllowed : Bool) : State :=
  { current := { Production.EffectProtocol.baseCurrent with
      review := { Production.EffectProtocol.baseReview with epoch := 9 } }
    cedarAllowed }

def envelope (state : State) : Envelope :=
  ⟨state.current.world, ⟨1,0⟩, state.current.effect, state.current.review,
    [state.current.authority.expected "world"]⟩

def row (label : String) (state : State) : Except String Lean.Json := do
  let receipt ← (Gateway.Lifecycle.invoke state (freshHandle state) (envelope state)).mapError (fun _ => "current-use Contract refused its actual result")
  return Lean.Json.mkObj [("label", Lean.toJson label), ("outcome", receipt.result.toJson),
    ("spent", Lean.toJson state.spent), ("sources_current", Lean.toJson state.sourcesCurrent), ("unknown", Lean.toJson state.current.unknown),
    ("revoked", Lean.toJson state.current.revoked), ("fact_generation", Lean.toJson state.factGeneration),
    ("now", Lean.toJson state.current.authority.now), ("epoch", Lean.toJson state.current.review.epoch)]

private def renewAt (state : State) (world : String) (cedarAllowed : Bool) : Except String State := do
  let fact := { Production.EffectProtocol.baseFact with
    source := world
    generation := state.factGeneration + 1
    notBefore := state.current.authority.now
    expiresAt := 200 }
  let authority : CedarPooSpec.ZeroTrust.FactAuthority String String :=
    ⟨fun _ => fact, fun _ => true, state.current.authority.now⟩
  let statements : List (CedarPooSpec.ZeroTrust.FactStatement String String) :=
    [⟨fact.issuer, 1, 0, [fact]⟩]
  let prepared ← ((sourceContract authority ["world"] (fun _ => true)).invoke
    (prepareStatements authority ["world"] (fun _ => true)) statements).mapError
      (fun _ => "source preparation Contract refused its actual fields")
  return renew state authority (prepared.result.map (·.field)) world cedarAllowed

private def intent : RetainedIntent := ⟨⟨"operation", [0], [1]⟩, "witness"⟩
private def cleanReport : AuditReport := ⟨[], [], [], [], [], 0, false⟩
private def evidence (committed : Bool) : RecoveryEvidence :=
  ⟨if committed then [intent.commit] else [], "witness", cleanReport, committed⟩

private def recoveryBoundaries (original : State) : Except String (List Lean.Json) := do
  if !original.cedarAllowed then return []
  let renewed ← renewAt original "source" true
  let uncertain := { renewed with
    spent := true
    retainedIntent := some intent
    current := { renewed.current with unknown := true } }
  let alternative : RecoveryEvidence :=
    ⟨[⟨"operation", [2], [3]⟩], "witness", cleanReport, true⟩
  if (recoverChecked uncertain alternative).isOk then throw "substituted history recovered"
  if (recoverChecked uncertain (evidence false)).isOk then throw "truncated history recovered"
  if (recoverChecked original (evidence true)).isOk then throw "unbound history recovered"
  return [← row "substituted-recovery" uncertain,
    ← row "truncated-recovery" uncertain, ← row "unbound-recovery" original]

private def providerTrust : ProviderAuditTrust :=
  ⟨"provider", "witness", fun source key outcome => key == "provider" && outcome.signature == [1] &&
    source.accepts Production.EffectProtocol.baseFact⟩

private def providerRecovery (original : State) (emptyAllowed worldChanged : Bool) : Except String (List Lean.Json) := do
  if !original.cedarAllowed then return []
  let pending := retainIntent original intent
  let action : AuditRecord := ⟨"operation", "original"⟩
  let outcome : ProviderOutcome :=
    ⟨⟨1,0⟩, "cedar-poo/provider-outcome", "witness", ⟨action, intent.commit⟩, [1]⟩
  let observed : ProviderRecoveryEvidence := ⟨[action], [outcome], [intent.commit], true, action⟩
  let missing ← recoverFromProviderChecked providerTrust pending {observed with outcomes := []}
  let invalid ← recoverFromProviderChecked providerTrust pending
    {observed with outcomes := [{outcome with signature := [0]}]}
  let unobserved ← recoverFromProviderChecked providerTrust pending {observed with actions := []}
  let complete ← recoverFromProviderChecked providerTrust pending observed
  let repeated ← recoverFromProviderChecked providerTrust complete observed
  let expired := { pending with current := { pending.current with
    authority := { pending.current.authority with now := 100 } } }
  let replaced := { expired with current := { expired.current with
    effect := { expired.current.effect with object := "replacement-incarnation", generation := 8 }
    mapped := false } }
  let controls ← recoverFromProviderChecked providerTrust (revoke replaced) observed
  let expiredResult ← recoverFromProviderChecked providerTrust expired observed
  let renewed ← renewAt expired "source" original.cedarAllowed
  let renewedResult ← recoverFromProviderChecked providerTrust renewed observed
  let quarantined := invalidateSources expired
  let quarantinedResult ← recoverFromProviderChecked providerTrust quarantined observed
  let repaired ← renewAt quarantined "source" original.cedarAllowed
  let repairedResult ← recoverFromProviderChecked providerTrust repaired observed
  let changed ← renewAt expired (if worldChanged then "empty-world" else "source") emptyAllowed
  let changedResult ← recoverFromProviderChecked providerTrust changed observed
  return [← row "provider-missing" missing, ← row "provider-invalid" invalid,
    ← row "provider-unobserved" unobserved, ← row "provider-complete" complete,
    ← row "provider-repeated" repeated, ← row "provider-current-controls" controls,
    ← row "provider-expired-current-audit" expiredResult,
    ← row "provider-renewed-current-audit" renewedResult,
    ← row "provider-quarantined-current-audit" quarantinedResult,
    ← row "provider-repaired-current-audit" repairedResult,
    ← row "provider-world-current-audit" changedResult]

/-- Outcomes are produced by actual POO Contract invocations; the Case producer
supplies real Cedar decisions for the current, empty-entity and held worlds. -/
def project (reviewed : Authorization.Delta.ReviewedInteraction) (model : PolicyModules.Model)
    (schema : Cedar.Validation.Schema) (originalAllowed emptyAllowed heldAllowed worldChanged : Bool) : Except String Lean.Json := do
  let original := seed originalAllowed
  let expired := { original with
    generation := original.generation + 1
    current := { original.current with authority := { original.current.authority with now := 100 } } }
  let renewed ← renewAt expired "source" originalAllowed
  let changed ← renewAt renewed (if worldChanged then "empty-world" else "source") emptyAllowed
  let aba ← renewAt changed "source" originalAllowed
  let held := { aba with
    generation := aba.generation + 1
    cedarAllowed := heldAllowed
    current := { aba.current with review := { aba.current.review with epoch := 10 } } }
  let failed := invalidateSources original
  let failedRecovered ← recoverChecked failed (evidence false)
  let repaired ← renewAt failedRecovered "source" originalAllowed
  let revoked := revoke original
  let spent := { original with
    spent := originalAllowed
    retainedIntent := if originalAllowed then some intent else none }
  let uncertain := { spent with current := { spent.current with unknown := originalAllowed } }
  let recoveredComplete ← recoverChecked spent (evidence originalAllowed)
  let unresolved := { evidence originalAllowed with
    report := if originalAllowed then { cleanReport with
      unresolvedPrecommits := ["operation"], missingReceipts := ["operation"] } else cleanReport }
  let recoveredUnknown ← recoverChecked uncertain unresolved
  let recoveredRevoked ← recoverChecked revoked (evidence false)
  let boundaries ← recoveryBoundaries original
  let providerStates ← providerRecovery original emptyAllowed worldChanged
  let active : Authorization.Delta.ReleaseState :=
    ⟨reviewed.snapshot.base.root, reviewed.snapshot.base.policies, .enforcing, reviewed.snapshot.epoch⟩
  let checked := (publicationContract reviewed model schema active changed "source" (envelope changed)).invoke
    (Gateway.ReviewedEffect.prepare reviewed model schema active ()) false
  return Lean.Json.mkObj [("publication", Lean.toJson checked.isOk), ("states", Lean.toJson ([← row "initial" original, ← row "expired" expired,
    ← row "renewed" renewed, ← row "entities" changed, ← row "world-aba" aba,
    ← row "policy" held, ← row "revoked" revoked,
    ← row "recovered-revoked" recoveredRevoked,
    ← row "recovered-complete" recoveredComplete,
    ← row "recovered-unknown" recoveredUnknown,
    ← row "failed-refresh" failed, ← row "recovered-failed-refresh" failedRecovered,
    ← row "repaired-refresh" repaired] ++ boundaries ++ providerStates))]
end CedarPooSpec.Production.Lifecycle
