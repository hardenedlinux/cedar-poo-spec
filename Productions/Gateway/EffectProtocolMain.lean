import Productions.Gateway.EffectProtocol

def main : IO Unit := do
  IO.FS.writeFile ".lake/build/gateway-effect-protocol.json"
    CedarPooSpec.Production.EffectProtocol.fixture.compress
  IO.println "EFFECT-PROTOCOL-ORACLE: 64 complete outcomes; shared across qualified domains"
