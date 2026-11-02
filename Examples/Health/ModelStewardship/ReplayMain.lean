import Examples.Health.ModelStewardship.ReplayExport

/-! Focused Cedar replay entry point for the medical model scenario. -/

def main (_args : List String) : IO Unit := do
  match CedarPooSpec.ModelStewardshipExample.ReplayExport.manifest.bind (·.toJson) with
  | .ok json => IO.println json.compress
  | .error message => throw (IO.userError message)
