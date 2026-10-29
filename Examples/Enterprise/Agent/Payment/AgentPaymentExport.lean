import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Payment.AgentPayment

namespace CedarPooSpec.AgentPaymentExport

open CedarPooSpec.AgentPaymentExample

def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, root, account, origin, requested, _) in cases do
    for ((layerRoot, req), index) in (checks root account origin requested).zipIdx do
      let receipt ← CedarPooSpec.AgentPaymentExample.paymentProgram.authorizationCase
          s!"{name}-layer-{index}" layerRoot.toLower layerRoot req paymentEntities
      rows := rows ++ [receipt]
  for ((root, req), index) in malformedChecks.zipIdx do
    let receipt ← CedarPooSpec.AgentPaymentExample.paymentProgram.authorizationCase
        s!"malformed-origin-layer-{index}" root.toLower root req paymentEntities
    rows := rows ++ [receipt]
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.AgentPaymentExport
