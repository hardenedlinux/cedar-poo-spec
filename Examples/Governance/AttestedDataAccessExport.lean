import Examples.Governance.AttestedDataAccess

/-! Export attested-data POO revisions and Lean-computed authorization receipts. -/

namespace CedarPooSpec.AttestedDataAccessExport

open CedarPooSpec.AttestedDataAccessExample
open CedarPooSpec.AttestedManifest

private def case (name : String) (root : Root) (req : Cedar.Spec.Request) :
    Except String CedarPooSpec.Transport.Case :=
  program.case name root.artifactRevision root.name req entities

def rows : Except String (List CedarPooSpec.Transport.Case) := do
  let stable ← LeanPoo.Functional.Validation.traverse (fun (name, req, _) => do
    let before ← case s!"{name}-baseline" .baseline req
    let after ← case s!"{name}-updated" .strengthened req
    return [before, after]) unchangedCases
  let staleBefore ← case "stale-attestation-baseline" .baseline
    (request customerDataset { attestationFresh := false })
  let staleAfter ← case "stale-attestation-updated" .strengthened
    (request customerDataset { attestationFresh := false })
  let inherited ← case "pre-integration-broad-permit" .ownerOnly
    (request financeDataset {})
  return stable.flatten ++ [staleBefore, staleAfter, inherited]

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  return { cases := (← rows) }

end CedarPooSpec.AttestedDataAccessExport
