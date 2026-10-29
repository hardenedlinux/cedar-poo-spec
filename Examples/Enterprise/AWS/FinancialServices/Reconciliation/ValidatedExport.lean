import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.AWS.FinancialServices.Reconciliation.Reconciliation
import CedarPooSpec.SchemaJson

namespace CedarPooSpec.AWS.Reconciliation.ValidatedExport

open CedarPooSpec.AWS.Reconciliation

def manifest : Except String Lean.Json := do
  let mut rows : List Lean.Json := []
  for (label, tool) in [
    ("ledger", searchLedger), ("notices", searchNotices),
    ("knowledge", retrieve), ("correspondence", searchCorrespondence),
    ("contacts", listContacts), ("templates", listTemplates),
    ("graph-list", graphList), ("graph-send", graphSend)] do
    for (root, variant) in [("SourceCombined", "source"),
                            ("OwnerCombined", "owners")] do
      let row ← CedarPooSpec.AWS.Reconciliation.program.authorizationCase
          s!"{variant}-{label}" variant root (readRequest agent tool) entities
      rows := rows ++ [row]
  for (name, root, req) in [
    ("worker-below-threshold", "OwnerCombined", writeRequest worker (some "84.9999")),
    ("worker-at-threshold", "OwnerCombined", writeRequest worker (some "85.0000")),
    ("worker-missing-confidence", "OwnerCombined", writeRequest worker none),
    ("human-without-confidence", "OwnerCombined", writeRequest platform none),
    ("raised-threshold-denies", "Threshold90", writeRequest worker (some "85.0000")),
    ("raised-threshold-allows", "Threshold90", writeRequest worker (some "90.0000")),
    ("agent-can-offer-confidence", "OwnerCombined", writeRequest agent (some "90.0000")),
    ("agent-status-denied", "OwnerCombined", readRequest agent updateStatus),
    ("platform-status-allowed", "OwnerCombined", readRequest platform updateStatus),
    ("paused-graph-send", "GraphPaused", readRequest agent graphSend),
    ("paused-wrapper-read", "GraphPaused", readRequest agent searchCorrespondence),
    ("paused-inner-read", "GraphPaused", readRequest agent graphList),
    ("joint-graph-send", "JointIncident", readRequest agent graphSend),
    ("recovered-graph-send", "Recovered", readRequest agent graphSend),
    ("joint-worker-85", "JointIncident", writeRequest worker (some "85.0000")),
    ("joint-worker-90", "JointIncident", writeRequest worker (some "90.0000"))] do
    let row ← CedarPooSpec.AWS.Reconciliation.program.authorizationCase name root root req entities
    rows := rows ++ [row]
  CedarPooSpec.SchemaJson.validatedManifest schema rows

end CedarPooSpec.AWS.Reconciliation.ValidatedExport
