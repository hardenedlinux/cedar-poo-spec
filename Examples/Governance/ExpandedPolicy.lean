import CedarPooSpec.Functional.CompilationJson
import Examples.Governance.TicketSharing

/-! A downstream-style Lean entrypoint that emits one compiled Cedar policy set. -/
def main : IO Unit :=
  match (CedarPooSpec.Functional.compilation CedarPooSpec.TicketSharingExample.expandedModel).export "Expanded" with
  | .ok json => IO.println json.compress
  | .error error => throw (IO.userError (reprStr error))
