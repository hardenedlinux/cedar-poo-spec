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
  let failedRecovered := recover failed false false
  let repaired ← renewAt failedRecovered "source" originalAllowed
  let revoked := revoke original
  let spent := { original with spent := originalAllowed }
  let uncertain := { spent with current := { spent.current with unknown := originalAllowed } }
  let recoveredComplete := recover spent originalAllowed originalAllowed
  let recoveredUnknown := recover uncertain originalAllowed false
  let active : Authorization.Delta.ReleaseState :=
    ⟨reviewed.snapshot.base.root, reviewed.snapshot.base.policies, .enforcing, reviewed.snapshot.epoch⟩
  let checked := (publicationContract reviewed model schema active changed "source" (envelope changed)).invoke
    (Gateway.ReviewedEffect.prepare reviewed model schema active ()) false
  return Lean.Json.mkObj [("publication", Lean.toJson checked.isOk), ("states", Lean.toJson [← row "initial" original, ← row "expired" expired,
    ← row "renewed" renewed, ← row "entities" changed, ← row "world-aba" aba,
    ← row "policy" held, ← row "revoked" revoked,
    ← row "recovered-revoked" (recover revoked false false),
    ← row "recovered-complete" recoveredComplete,
    ← row "recovered-unknown" recoveredUnknown,
    ← row "failed-refresh" failed, ← row "recovered-failed-refresh" failedRecovered,
    ← row "repaired-refresh" repaired])]
end CedarPooSpec.Production.Lifecycle
