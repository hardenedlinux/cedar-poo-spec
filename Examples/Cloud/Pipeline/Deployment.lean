import CedarPooSpec.Functional.Capabilities
import Examples.Cloud.Pipeline.GoogleThreatCase

/-! Only complete pipeline roots can be selected for publication. Stage roots
remain observable for regression cases but are not deployment choices. -/

namespace CedarPooSpec.Cloud.Pipeline.GoogleThreatCase.Deployment

open CedarPooSpec.Cloud.Pipeline.GoogleThreatCase

inductive Root where
  | releaseReady
  | quarantined
  | recovered
  deriving DecidableEq, Repr

def Root.name : Root → String
  | .releaseReady => "ReleaseReady"
  | .quarantined => "Quarantined"
  | .recovered => "Recovered"

def publish (root : Root) :=
  CedarPooSpec.Cloud.Pipeline.GoogleThreatCase.program.publish root.name

end CedarPooSpec.Cloud.Pipeline.GoogleThreatCase.Deployment
