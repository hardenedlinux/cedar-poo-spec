import Tests.Functional.Profiles

def main (args : List String) : IO Unit := do
  CedarPooSpec.FunctionalProfilesTest.runNative
  match args with
  | ["--checks-only"] => pure ()
  | [] => CedarPooSpec.FunctionalProfilesTest.runWorkloads none
  | ["--probe", name] => CedarPooSpec.FunctionalProfilesTest.runWorkloads (some name)
  | _ => throw (IO.userError "usage: objectProfilesNative [--probe NAME|--checks-only]")
