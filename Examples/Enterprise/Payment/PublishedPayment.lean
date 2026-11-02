import Examples.Enterprise.Payment.PaymentRelease

/-! Emit the integrated payment policy set after Lean Cedar validation. -/

def main : IO Unit :=
  match CedarPooSpec.PaymentReleaseExample.program.publish "Integrated" with
  | .ok publication => IO.println publication.json.compress
  | .error error => throw (IO.userError error.message)
