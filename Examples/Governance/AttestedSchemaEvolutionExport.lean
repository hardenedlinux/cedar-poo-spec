import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.SchemaJson
import Examples.Governance.AttestedDataAccess

/-! Recheck one compiled POO root against both versions of its entity schema. -/

namespace CedarPooSpec.AttestedSchemaEvolutionExport

open CedarPooSpec.AttestedDataAccessExample
open CedarPooSpec.AttestedManifest

private def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AttestedDataAccessExample.model CedarPooSpec.AttestedDataAccessExample.schema :=
      CedarPooSpec.AttestedDataAccessExample.program) (candidate : Cedar.Validation.Schema) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, req, _) in unchangedCases do
    let receipt ← owner.case
        name Root.strengthened.artifactRevision Root.strengthened.name req entities
    rows := rows ++ [receipt]
  let stale ← owner.case
      "stale-attestation" Root.strengthened.artifactRevision Root.strengthened.name (request customerDataset { attestationFresh := false }) entities
  CedarPooSpec.SchemaJson.manifest candidate (rows ++ [stale])

def bundle
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AttestedDataAccessExample.model CedarPooSpec.AttestedDataAccessExample.schema :=
      CedarPooSpec.AttestedDataAccessExample.program) : Except String CedarPooSpec.Transport.Entry := do
  return .evolution (← (manifest (owner := owner)) schema) (← (manifest (owner := owner)) schemaWithClassification)

end CedarPooSpec.AttestedSchemaEvolutionExport
