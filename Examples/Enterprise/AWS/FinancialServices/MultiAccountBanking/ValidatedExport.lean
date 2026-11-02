import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.AWS.FinancialServices.MultiAccountBanking.MultiAccountBanking
import CedarPooSpec.SchemaJson

namespace CedarPooSpec.MultiAccountBankingValidatedExport

open CedarPooSpec.MultiAccountBankingExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (label, action) in [
    ("customer", customer), ("accounts", accounts), ("balance", balance),
    ("profile", profile), ("update-balance", updateBalance),
    ("delete-customer", deleteCustomer), ("payments", payments),
    ("transfer", transfer), ("beneficiaries", beneficiaries),
    ("schedule-payment", schedulePayment), ("loans", loans),
    ("credit-score", creditScore), ("eligibility", eligibility),
    ("emi-details", emiDetails), ("calculate-emi", calculateEmi),
    ("lending-policy", lendingPolicy), ("tools-list", listTools),
    ("initialize", initializeAction)] do
    for (root, variant) in [("SampleBroad", "source"),
                            ("OwnerCombined", "owners")] do
      let row ← owner.case
          s!"{variant}-{label}" variant root (request banker action) entities
      rows := rows ++ [row]
  for (root, variant, label, action) in [
    ("TransferPaused", "paused", "transfer", transfer),
    ("TransferPaused", "paused", "payments", payments),
    ("TransferPaused", "paused", "balance", balance),
    ("TransferPaused", "paused", "delete-customer", deleteCustomer),
    ("TransferResumed", "resumed", "transfer", transfer)] do
    let row ← owner.case
        s!"{variant}-{label}" variant root (request banker action) entities
    rows := rows ++ [row]
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.MultiAccountBankingValidatedExport
