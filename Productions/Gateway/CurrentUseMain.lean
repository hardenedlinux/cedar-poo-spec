import Productions.Gateway.CurrentUse

def main : IO Unit := do
  let fixture ← IO.ofExcept CedarPooSpec.Production.CurrentUse.fixture
  IO.FS.writeFile ".lake/build/gateway-production-current-use.json" fixture.compress
  IO.println "GATEWAY-PRODUCTION-CURRENT-USE: 4 Cedar worlds; 24 release-bound uses"
