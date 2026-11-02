import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.AWS.FinancialServices.LakehouseGateway.LakehouseGateway
import CedarPooSpec.SchemaJson

namespace CedarPooSpec.LakehouseGatewayValidatedExport

open CedarPooSpec.LakehouseGatewayExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.LakehouseGatewayExample.model CedarPooSpec.LakehouseGatewayExample.schema :=
      CedarPooSpec.LakehouseGatewayExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, user, action, location, _) in sourceCases do
    let source ← owner.case
        name "source-combined" "SourceCombined" (request user action location) entities
    let hardened ← owner.case
        s!"hardened-{name}" "fail-closed" "FailClosed" (request user action location) entities
    rows := rows ++ [source, hardened]
  for (label, location) in [("missing", none), ("unknown", some "UNKNOWN")] do
    for root in ["SourceCombined", "FailClosed"] do
      let row ← owner.case
          s!"{root.toLower}-{label}-geography" root.toLower root (request adjusterUS queryClaims location) entities
      rows := rows ++ [row]
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.LakehouseGatewayValidatedExport
