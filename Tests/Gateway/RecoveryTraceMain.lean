import Tests.Gateway.OAuthRefresh

def main : IO Unit := do
  unless Tests.Gateway.OAuthRefresh.recoveryPlanValidated do
    throw (IO.userError "OAuth recovery plan failed its typed Contract replay")
  (← IO.getStdout).putStrLn Tests.Gateway.RecoveryPlan.fixture.compress
