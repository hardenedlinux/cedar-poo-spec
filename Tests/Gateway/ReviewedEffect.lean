import CedarPooSpec.Gateway.ReviewedEffect
import Productions.Gateway.ReviewedEffects

open CedarPooSpec.Gateway.ReviewedEffect
#print axioms invocation_installs_exact_successor
#print axioms invocation_then_current_effect
#print axioms actual_final_then_current_effect
#print axioms CedarPooSpec.Transport.SchemaSource.wire_bound

-- Compiled model/root provenance is proof-bearing; an arbitrary alias is not.
#check_failure fun (source : CedarPooSpec.Transport.PolicySource)
    (origin : CedarPooSpec.Transport.PolicyOrigin source.policies) =>
  ({ origin with root := "unreviewed-root", compiled := rfl } :
    CedarPooSpec.Transport.PolicyOrigin source.policies)
