import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Procurement.DelegatedApproval

/-! A policy artifact is emitted only after schema and policy validation. -/
def main : IO Unit :=
  match CedarPooSpec.DelegatedApprovalExample.delegatedProgram.publish "Delegated" with
  | .ok publication => IO.println publication.json.compress
  | .error (.context _ (.composition _)) => throw (IO.userError "POO composition failed")
  | .error (.context _ (.schema _)) => throw (IO.userError "Cedar schema is invalid")
  | .error (.context _ (.policy _)) => throw (IO.userError "Cedar policy validation failed")
  | .error (.context _ (.export _)) => throw (IO.userError "Cedar export failed")
  | .error (.context _ .duplicatePolicyIds) => throw (IO.userError "Cedar policy IDs are not unique")
  | .error (.missingCapability key) => throw (IO.userError s!"missing Cedar capability: {repr key}")
