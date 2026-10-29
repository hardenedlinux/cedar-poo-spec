import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson
import CedarPooSpec.SchemaJson
import Examples.Governance.AttestedDataAccess

/-! Recheck one compiled POO root against both versions of its entity schema. -/

namespace CedarPooSpec.AttestedSchemaEvolutionExport

open CedarPooSpec.AttestedDataAccessExample
open CedarPooSpec.AttestedManifest

private def manifest (candidate : Cedar.Validation.Schema) : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (name, req, _) in unchangedCases do
    let receipt ← CedarPooSpec.AttestedDataAccessExample.program.authorizationCase
        name Root.strengthened.artifactRevision Root.strengthened.name req entities
    rows := rows ++ [receipt]
  let stale ← CedarPooSpec.AttestedDataAccessExample.program.authorizationCase
      "stale-attestation" Root.strengthened.artifactRevision Root.strengthened.name (request customerDataset { attestationFresh := false }) entities
  CedarPooSpec.SchemaJson.validatedManifest candidate (rows ++ [stale])

def bundle : Except String Lean.Json := do
  return Lean.Json.mkObj [
    ("before", ← manifest schema),
    ("after", ← manifest schemaWithClassification)]

end CedarPooSpec.AttestedSchemaEvolutionExport
