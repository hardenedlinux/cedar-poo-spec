import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.AWS.FinancialServices.LakehouseGateway.LakehouseGateway
import CedarPooSpec.SchemaJson

namespace CedarPooSpec.LakehouseGatewayValidatedExport

open CedarPooSpec.LakehouseGatewayExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, user, action, location, _) in sourceCases do
    let source ← CedarPooSpec.LakehouseGatewayExample.program.case
        name "source-combined" "SourceCombined" (request user action location) entities
    let hardened ← CedarPooSpec.LakehouseGatewayExample.program.case
        s!"hardened-{name}" "fail-closed" "FailClosed" (request user action location) entities
    rows := rows ++ [source, hardened]
  for (label, location) in [("missing", none), ("unknown", some "UNKNOWN")] do
    for root in ["SourceCombined", "FailClosed"] do
      let row ← CedarPooSpec.LakehouseGatewayExample.program.case
          s!"{root.toLower}-{label}-geography" root.toLower root (request adjusterUS queryClaims location) entities
      rows := rows ++ [row]
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.LakehouseGatewayValidatedExport
