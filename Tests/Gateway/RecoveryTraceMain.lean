import Tests.Gateway.OAuthRefresh

def main : IO Unit := do
  unless Tests.Gateway.OAuthRefresh.recoveryPlanValidated do
    throw (IO.userError "OAuth recovery plan failed its typed Contract replay")
  IO.FS.writeFile ".lake/build/gateway-settled-late-plan.json"
    Tests.Gateway.SettledLatePlan.fixture.compress
  let profiles ← IO.ofExcept (Tests.Gateway.CurrentCommit.profiles.mapError IO.userError)
  IO.FS.writeFile ".lake/build/gateway-current-commit-profiles.json" profiles.compress
  IO.FS.writeFile ".lake/build/gateway-payment-crash-plan.json"
    Tests.Gateway.CurrentCommit.paymentCrashPlan.compress
  IO.FS.writeFile ".lake/build/gateway-payment-concurrent-plan.json"
    Tests.Gateway.CurrentCommit.paymentConcurrentPlan.compress
  IO.FS.writeFile ".lake/build/gateway-payment-recrash-plan.json"
    Tests.Gateway.CurrentCommit.paymentRecrashPlan.compress
  (← IO.getStdout).putStrLn Tests.Gateway.RecoveryPlan.fixture.compress
