import Examples.Enterprise.Personnel.SourceCustody
import CedarPooSpec.SchemaJson

namespace CedarPooSpec.SourceCustodyValidatedExport

open CedarPooSpec.SourceCustodyExample

def scenarios : List (String × String × Cedar.Spec.Entities ×
    CedarPooSpec.Governance.Personnel.AssetAccess.Operation) := [
  ("core-read", "SmallTeam", entities, normalRead),
  ("stolen-device-read", "SmallTeam", entities, stolenRead),
  ("researcher-shared-read", "SmallTeam", entities, researcherRead),
  ("researcher-crown-read", "SmallTeam", entities, researcherCrown),
  ("intern-shared-read", "SmallTeam", entities, internSharedRead),
  ("intern-project-read", "SmallTeam", entities, internResearchRead),
  ("intern-project-download", "SmallTeam", entities, internResearchDownload),
  ("researcher-a-project-read", "SmallTeam", entities, researcherARead),
  ("researcher-a-cross-project-read", "SmallTeam", entities, researcherAWrongProjectRead),
  ("researcher-b-project-read", "SmallTeam", entities, researcherBRead),
  ("isolated-integration-interface", "Isolated", entities, researcherAInterfaceRead),
  ("scoped-integration-interface", "SmallTeam", entities, researcherAInterfaceRead),
  ("scoped-integration-full-source", "SmallTeam", entities, researcherAFullBRead),
  ("researcher-a-project-download", "SmallTeam", entities, researcherADownload),
  ("researcher-b-cross-project-download", "SmallTeam", entities, researcherBWrongDownload),
  ("core-product-download", "SmallTeam", entities, founderDownload),
  ("core-restricted-download", "SmallTeam", entities, founderCrownDownload),
  ("agent-without-delegation", "SmallTeam", entities, agentReadWithoutDelegation),
  ("agent-with-delegation", "SmallTeam", entities, agentReadWithDelegation),
  ("agent-expired-delegation", "SmallTeam", entities, agentReadAfterExpiry),
  ("approved-release", "SmallTeam", entities, approvedRelease 1),
  ("revoked-approval-release", "SmallTeam", entities, approvedRelease 2),
  ("core-component-read", "SmallTeam", entities, normalSliceRead),
  ("unapproved-external-transfer", "SmallTeam", entities, attemptedExternalTransfer),
  ("agent-external-transfer", "SmallTeam", entities, attemptedAgentTransfer),
  ("agent-read-grant-cannot-release", "SmallTeam", entities, agentRelease readDelegation),
  ("agent-explicit-release", "SmallTeam", entities, agentRelease releaseDelegation),
  ("partial-code-sale", "SmallTeam", entities, attemptedPartialSale),
  ("departure-internal-read", "SmallTeam", departingEntities, normalRead),
  ("departure-blocks-download", "SmallTeam", departingEntities, founderDownload),
  ("departure-blocks-approved-release", "SmallTeam", departingEntities, approvedRelease 1),
  ("separation-revokes-read", "SmallTeam", separatedEntities, normalRead),
  ("separation-revokes-agent", "SmallTeam", separatedEntities, agentReadWithDelegation),
  ("crown-external-release", "SmallTeam", entities, crownRelease),
  ("partner-before-extension", "SmallTeam", entities, partnerReadOperation),
  ("partner-after-extension", "LargeTeam", entities, partnerReadOperation),
  ("reported-incident-release", "LargeTeam", entities, incidentRelease),
  ("incident-freeze-release", "Incident", entities, approvedRelease 1),
  ("incident-still-reads", "Incident", entities, normalRead),
  ("recovered-release", "Recovered", entities, approvedRelease 1)]

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.SourceCustodyExample.model CedarPooSpec.SourceCustodyExample.schema :=
      CedarPooSpec.SourceCustodyExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← LeanPoo.Functional.Validation.traverse (fun (name, root, store, operation) =>
    owner.case name root root
      operation.request store) scenarios
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.SourceCustodyValidatedExport
