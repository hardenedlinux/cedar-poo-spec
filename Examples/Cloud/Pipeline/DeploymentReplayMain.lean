import Examples.Cloud.Pipeline.DeploymentReplayExport

def main : IO Unit := do
  match CedarPooSpec.Cloud.Pipeline.DeploymentCase.manifest.bind (·.toJson) with
  | .ok value => IO.println value.compress
  | .error error => throw <| IO.userError error
