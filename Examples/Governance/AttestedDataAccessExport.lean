import Examples.Governance.AttestedDataAccess

/-! Export attested-data POO revisions and Lean-computed authorization receipts. -/

namespace CedarPooSpec.AttestedDataAccessExport

open CedarPooSpec.AttestedDataAccessExample
open CedarPooSpec.AttestedManifest

private def case
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AttestedDataAccessExample.model CedarPooSpec.AttestedDataAccessExample.schema :=
      CedarPooSpec.AttestedDataAccessExample.program) (name : String) (root : Root) (req : Cedar.Spec.Request) :
    Except String CedarPooSpec.Transport.Case :=
  owner.case name root.artifactRevision root.name req entities

def rows
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AttestedDataAccessExample.model CedarPooSpec.AttestedDataAccessExample.schema :=
      CedarPooSpec.AttestedDataAccessExample.program) : Except String (List CedarPooSpec.Transport.Case) := do
  let stable ← LeanPoo.Functional.Validation.traverse (fun (name, req, _) => do
    let before ← (case (owner := owner)) s!"{name}-baseline" .baseline req
    let after ← (case (owner := owner)) s!"{name}-updated" .strengthened req
    return [before, after]) unchangedCases
  let staleBefore ← (case (owner := owner)) "stale-attestation-baseline" .baseline
    (request customerDataset { attestationFresh := false })
  let staleAfter ← (case (owner := owner)) "stale-attestation-updated" .strengthened
    (request customerDataset { attestationFresh := false })
  let inherited ← (case (owner := owner)) "pre-integration-broad-permit" .ownerOnly
    (request financeDataset {})
  return stable.flatten ++ [staleBefore, staleAfter, inherited]

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AttestedDataAccessExample.model CedarPooSpec.AttestedDataAccessExample.schema :=
      CedarPooSpec.AttestedDataAccessExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  return { cases := (← (rows (owner := owner))) }

end CedarPooSpec.AttestedDataAccessExport
