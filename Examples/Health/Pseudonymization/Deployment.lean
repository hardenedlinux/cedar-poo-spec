import Examples.Health.Pseudonymization

/-!
Only an explicitly selected governed root can become a deployment artifact.
The unsafe migration ancestor remains available to negative authorization
fixtures but has no constructor in this publication contract.
-/

namespace CedarPooSpec.PseudonymizationExample.Deployment

open CedarPooSpec.PseudonymizationExample

inductive Root where
  | hospitalSiv
  | randomizedGcm
  | oneWayHmac
  | resultRelease
  | agentIncident
  | recovered
  deriving BEq, Repr

def Root.name : Root → String
  | .hospitalSiv => PseudonymizationExample.hospitalView.name
  | .randomizedGcm => PseudonymizationExample.randomizedView.name
  | .oneWayHmac => PseudonymizationExample.oneWayView.name
  | .resultRelease => PseudonymizationExample.resultRelease.name
  | .agentIncident => PseudonymizationExample.incident.name
  | .recovered => PseudonymizationExample.recovered.name

def publish (root : Root) :=
  program.publish root.name

end CedarPooSpec.PseudonymizationExample.Deployment
