import Tests.Gateway.Fixture

open CedarPooSpec CedarPooSpec.GatewayTest

private def checkedPlan (before after : String) : IO Gateway.DeltaPlan :=
  match Gateway.prepareDelta model before after schema scope scope with
  | .ok plan => pure plan
  | .error error => throw (IO.userError s!"Gateway Delta preparation: {repr error}")

private def analyzePlan (plan : Gateway.DeltaPlan) := do
  match ← plan.analyze with
  | .ok report => pure report
  | .error error => throw (IO.userError s!"Gateway Delta analysis: {repr error}")

def main : IO Unit := do
  let restriction ← checkedPlan "base" "restricted"
  let restrictive ← analyzePlan restriction
  unless restrictive.gains.isEmpty && !restrictive.losses.isEmpty do
    throw (IO.userError "Gateway freeze did not have exact loss-only execution Delta")
  let expansion ← checkedPlan "restricted" "base"
  let expanding ← analyzePlan expansion
  unless !expanding.gains.isEmpty && expanding.losses.isEmpty do
    throw (IO.userError "Gateway unfreeze did not expose execution-gain witnesses")
  let unchanged ← checkedPlan "base" "base"
  let same ← analyzePlan unchanged
  unless same.gains.isEmpty && same.losses.isEmpty do
    throw (IO.userError "Gateway identity revision changed execution")
  unless restriction.matchesCurrent model scope &&
      !restriction.matchesCurrent replacedModel scope &&
      !restriction.matchesCurrent model { scope with sourceCut := "source-2" } do
    throw (IO.userError "Gateway Delta accepted stale policies or source scope")
  IO.println s!"GATEWAY-DELTA-OK: {restrictive.environmentsChecked} environments; loss/gain/equivalence and stale binding controls"
