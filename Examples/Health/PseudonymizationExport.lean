import CedarPooSpec.SchemaJson
import Examples.Health.Pseudonymization
import Examples.Health.Pseudonymization.Deployment
import Examples.Health.Pseudonymization.Lifecycle

/-! Export each composed root with the same source and target entities used by
the Lean decision proof. Rust Cedar validates the schema and replays the cases. -/

namespace CedarPooSpec.PseudonymizationExport

open CedarPooSpec.PseudonymizationExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.PseudonymizationExample.model CedarPooSpec.PseudonymizationExample.schema :=
      CedarPooSpec.PseudonymizationExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  unless hmacCatalogSeparated datasets do
    throw "cross-scope HMAC key reuse in published dataset catalog"
  let rows ← LeanPoo.Functional.Validation.traverse (fun (name, root, req, _) =>
    owner.case name root root req entities) cases
  CedarPooSpec.SchemaJson.manifest schema rows

def deployableRoots : List PseudonymizationExample.Deployment.Root :=
  [.hospitalSiv, .randomizedGcm, .oneWayHmac,
   .resultRelease, .agentIncident, .recovered]

/-- Deployment artifacts have a typed allowlist; the migration ancestor is
    available only to the authorization regression manifest above. -/
def deploymentManifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.PseudonymizationExample.model CedarPooSpec.PseudonymizationExample.schema :=
      CedarPooSpec.PseudonymizationExample.program) : Except String (List CedarPooSpec.Transport.PolicyArtifact) := do
  unless hmacCatalogSeparated datasets do
    throw "cross-scope HMAC key reuse in published dataset catalog"
  let roots ← LeanPoo.Functional.Validation.traverse (fun root => do
    let publication ← (owner.publish root.name).mapError
      (fun _ => "deployable root failed Cedar publication")
    return { root := root.name, source := publication.snapshot }) deployableRoots
  return roots

end CedarPooSpec.PseudonymizationExport
