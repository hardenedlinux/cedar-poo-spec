import CedarPooSpec.Functional.Capabilities
import Examples.Scenarios.TenantDevicePolicyEvolution
import CedarPooSpec.PolicyJson

/-! Export every POO revision and named tenant/device decision to Cedar Rust. -/

namespace CedarPooSpec.TenantDevicePolicyEvolutionExport

open CedarPooSpec.TenantDeviceAuthorizationExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.TenantDeviceAuthorizationExample.model CedarPooSpec.TenantDeviceAuthorizationExample.schema :=
      CedarPooSpec.TenantDeviceAuthorizationExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← expectedDecisions.zipIdx.mapM fun ((root, req, _), index) =>
    owner.case
        s!"{root.toLower}-case-{index}" root.toLower root req entities
  return { cases := rows }

end CedarPooSpec.TenantDevicePolicyEvolutionExport
