import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.AWS.FinancialServices.LakehouseGateway.LakehouseGateway
import CedarPooSpec.SchemaJson

namespace CedarPooSpec.LakehouseGatewayValidatedExport

open CedarPooSpec.LakehouseGatewayExample

def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, user, action, location, _) in sourceCases do
    let source ← CedarPooSpec.LakehouseGatewayExample.program.authorizationCase
        name "source-combined" "SourceCombined" (request user action location) entities
    let hardened ← CedarPooSpec.LakehouseGatewayExample.program.authorizationCase
        s!"hardened-{name}" "fail-closed" "FailClosed" (request user action location) entities
    rows := rows ++ [source, hardened]
  for (label, location) in [("missing", none), ("unknown", some "UNKNOWN")] do
    for root in ["SourceCombined", "FailClosed"] do
      let row ← CedarPooSpec.LakehouseGatewayExample.program.authorizationCase
          s!"{root.toLower}-{label}-geography" root.toLower root (request adjusterUS queryClaims location) entities
      rows := rows ++ [row]
  CedarPooSpec.SchemaJson.validatedManifest schema rows

end CedarPooSpec.LakehouseGatewayValidatedExport
