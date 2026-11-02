import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Payment.AgentPayment

namespace CedarPooSpec.AgentPaymentExport

open CedarPooSpec.AgentPaymentExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AgentPaymentExample.paymentModel CedarPooSpec.AgentPaymentExample.paymentSchema :=
      CedarPooSpec.AgentPaymentExample.paymentProgram) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, root, account, origin, requested, _) in cases do
    for ((layerRoot, req), index) in (checks root account origin requested).zipIdx do
      let receipt ← owner.case
          s!"{name}-layer-{index}" layerRoot.toLower layerRoot req paymentEntities
      rows := rows ++ [receipt]
  for ((root, req), index) in malformedChecks.zipIdx do
    let receipt ← owner.case
        s!"malformed-origin-layer-{index}" root.toLower root req paymentEntities
    rows := rows ++ [receipt]
  return { cases := rows }

end CedarPooSpec.AgentPaymentExport
