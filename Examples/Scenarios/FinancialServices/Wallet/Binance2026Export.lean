import Examples.Scenarios.FinancialServices.Wallet.Binance2026Replay
import Lean.Data.Json

namespace CedarPooSpec.Binance2026Scenario

private def quoted (text : String) : String := (Lean.toJson text).compress
private def name (cap : Capability) : String := ((reprStr cap).splitOn ".").getLast!
private def setOf (items : List String) : String := "Set(" ++ String.intercalate ", " items ++ ")"

/-- Quint consumes the actual checked POO model; no second compromise graph is
maintained in the finite-state case. Generation fails when either parent drops. -/
private def exportProfile (instanceName importedModule importPath : String)
    (expected : CedarPooSpec.Attackers.ProfileObject.Model Capability) : Except String String := do
  let checked ← match selectedModel with
    | some model => .ok model
    | none => .error "attacker object admission failed"
  if checked.model != expected then
    .error "scenario/attacker model mismatch"
  let initial := setOf (checked.model.initial.map (quoted ∘ name))
  let isolated := setOf (checked.model.isolated.map (quoted ∘ name))
  let goals := setOf (checked.model.goals.map quoted)
  let rules := setOf (checked.model.rules.map fun rule =>
    "{ needs: " ++ setOf (rule.requires.map (quoted ∘ name)) ++ ", grants: " ++ quoted (name rule.grants) ++ " }")
  pure (String.intercalate "\n" [
    "// Generated from checked LeanPoo slots; do not edit.",
    "module " ++ instanceName ++ " {",
    "  pure val ProfileInitial: Set[str] = " ++ initial,
    "  pure val ProfileIsolated: Set[str] = " ++ isolated,
    "  pure val ProfileGoals: Set[str] = " ++ goals,
    "  pure val ProfileRules: Set[{needs: Set[str], grants: str}] = " ++ rules,
    "  import " ++ importedModule ++ "(Initial = ProfileInitial, Isolated = ProfileIsolated, Goals = ProfileGoals, Rules = ProfileRules).* from " ++ quoted importPath,
    "}", ""])

def exportQuint : Except String String := exportProfile "wallet_attackers_case" "wallet_signing"
  "../../dev/qnt/financial/WalletSigning" scenario.model.2.model

def exportReplayQuint : Except String String := do
  if !(CedarPooSpec.Scenarios.Replay.valid Replay.scenario.metadata.value Replay.stages) then
    .error "invalid replay provenance"
  exportProfile "wallet_replay_case" "wallet_replay"
    "../../dev/qnt/financial/WalletReplay" Replay.scenario.model.2.model

private def fullSummaryJson (value : Replay.Summary) : Lean.Json := Lean.Json.mkObj [
  ("signer_reachable", Lean.toJson value.signerReachable), ("signing_intents", Lean.toJson value.signingIntents),
  ("paused", Lean.toJson value.paused), ("delegated", Lean.toJson value.delegated),
  ("delegated_uses", Lean.toJson value.delegatedUses), ("settled", Lean.toJson value.settled),
  ("refused", Lean.toJson value.refused), ("unknown", Lean.toJson value.unknown)]

private def fullFrameJson (frame : CedarPooSpec.Scenarios.Replay.Description × Replay.Summary) : Lean.Json :=
  Lean.Json.mkObj [("stage", Lean.toJson frame.1.id), ("state", fullSummaryJson frame.2)]

private def replayLaneJson (id : String) (mode : Replay.Mode) (initial : Replay.State) : Except String Lean.Json := do
  let (frames, _) ← CedarPooSpec.Scenarios.Replay.prepare Replay.scenario.metadata.value
    (Replay.step mode) Replay.summarize initial Replay.stages
  pure (Lean.Json.mkObj [("id", Lean.toJson id), ("frames", Lean.toJson (frames.map fullFrameJson))])

def exportReplayVisual : Except String Lean.Json := do
  let legitimate := CedarPooSpec.Attackers.run (Replay.surface .guarded)
    { Replay.clean.attacker with known := [.signerNetwork, .signerCredential] }
    [.call CedarPooSpec.WalletSigningExample.request, .call CedarPooSpec.WalletSigningExample.request]
  let lanes : List (String × Replay.Mode × Replay.State) := [("bypass-countermodel", Replay.Mode.bypassCountermodel, Replay.clean),
    ("guarded-clean", Replay.Mode.guarded, Replay.clean),
    ("guarded-prior", Replay.Mode.guarded, Replay.priorExposure)]
  let observed ← lanes.mapM fun (id, mode, initial) => replayLaneJson id mode initial
  pure (Lean.Json.mkObj [
    ("provenance", Replay.scenario.provenanceJson),
    ("legitimate_once", Lean.toJson (legitimate.outputs.length == 1)),
    ("stages", Lean.toJson (Replay.stages.map fun stage => Lean.Json.mkObj [
      ("id", Lean.toJson stage.description.id), ("title", Lean.toJson stage.description.title),
      ("basis", Lean.toJson (match stage.description.basis with
        | .reported => "reported" | .assumed => "assumed" | .probe => "probe")),
      ("source", Lean.toJson stage.description.source), ("at_utc", Lean.toJson stage.description.atUTC),
      ("limitation", Lean.toJson stage.description.limitation)])),
    ("lanes", Lean.toJson observed)])

private def replayJson (stage : ReplayStage) : Lean.Json := Lean.Json.mkObj [
  ("id", Lean.toJson stage.id), ("reported_on", Lean.toJson stage.reportedOn),
  ("reached", Lean.toJson stage.reached), ("signer_reachable", Lean.toJson stage.signerReachable),
  ("signatures", Lean.toJson stage.signatures), ("refused", Lean.toJson stage.refused)]

private def containmentJson (observed : Containment.Observation) : Lean.Json := Lean.Json.mkObj [
  ("id", Lean.toJson observed.id), ("paused", Lean.toJson observed.paused),
  ("delegated", Lean.toJson observed.delegated), ("revoked", Lean.toJson observed.revoked),
  ("signature_released", Lean.toJson observed.signatureReleased)]

/-- Observed synthetic outcomes for source-bound diagrams, not production telemetry. -/
def exportVisual : Except String Lean.Json := do
  let replay ← exportReplayVisual
  let request := scenario.model.1.2
  pure (Lean.Json.mkObj [
    ("provenance", scenario.provenanceJson),
    ("replay", replay),
    ("attack", Lean.toJson (replayStages.map replayJson)),
    ("containment", Lean.toJson (Containment.observations.map containmentJson)),
    ("host", Lean.toJson (HostBoundary.observations.map fun observed => Lean.Json.mkObj [
      ("id", Lean.toJson observed.id), ("admitted", Lean.toJson observed.admitted)])),
    ("defense", Lean.Json.mkObj [
      ("deployment_refused", Lean.toJson (CedarPooSpec.Vertical.FinancialServices.PaymentContainment.release
        Containment.clean deploymentRequest).isNone),
      ("valid_transfer_released", Lean.toJson (CedarPooSpec.Vertical.FinancialServices.PaymentContainment.release
        Containment.clean request).isSome)])])


end CedarPooSpec.Binance2026Scenario

open CedarPooSpec.Binance2026Scenario in
def main (args : List String) : IO Unit :=
  match args with
  | ["visual"] => match CedarPooSpec.Binance2026Scenario.exportVisual with
    | .ok observed => IO.println observed.compress
    | .error error => throw (IO.userError error)
  | ["replay"] => do
    IO.println "Synthetic disclosed-chain replay; intents are not signatures or blockchain execution."
    for (id, mode, initial) in [("BYPASS COUNTERMODEL", Replay.Mode.bypassCountermodel, Replay.clean),
        ("GUARDED CLEAN", Replay.Mode.guarded, Replay.clean),
        ("GUARDED PRIOR EXPOSURE", Replay.Mode.guarded, Replay.priorExposure)] do
      IO.println id
      let observed ← match CedarPooSpec.Scenarios.Replay.prepare Replay.scenario.metadata.value
          (Replay.step mode) Replay.summarize initial Replay.stages with
        | .ok (frames, _) => pure frames
        | .error error => throw (IO.userError error)
      for (stage, value) in observed do
        IO.println s!"  {stage.id}: intents={value.signingIntents} pause={value.paused} delegation={value.delegated} delegated_uses={value.delegatedUses} settled={value.settled}"
  | ["replay-quint"] => match CedarPooSpec.Binance2026Scenario.exportReplayQuint with
    | .ok source => IO.print source
    | .error error => throw (IO.userError error)
  | ["metadata"] => IO.println CedarPooSpec.Binance2026Scenario.scenario.provenanceJson.compress
  | [] => match CedarPooSpec.Binance2026Scenario.exportQuint with
    | .ok source => IO.print source
    | .error error => throw (IO.userError error)
  | _ => throw (IO.userError "expected no arguments, metadata, visual, replay or replay-quint")
