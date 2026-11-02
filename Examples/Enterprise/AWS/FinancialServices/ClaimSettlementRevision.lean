import Examples.Enterprise.AWS.FinancialServices.ClaimSettlement
import LeanPoo.Proof.Reuse

/-! The transaction-owner overlay changes the banking decision. The
insurance Gateway decision depends on a different key, so its certificate
can be transported by LeanPOO's public reuse theorem. -/

namespace CedarPooSpec.AWS.ClaimSettlementRevision

open LeanPoo.Proof

inductive Owner where
  | claims
  | bank
  deriving DecidableEq, BEq, Repr

def Value (_ : Owner) : Type := Bool

def obligation (owner : Owner) : Obligation Owner Value where
  dependencies := [owner]
  holds := fun state => state owner = true
  stable := by
    intro before after agreement result
    exact (agreement owner (by simp)).symm.trans result

def claimsObligation : Obligation Owner Value := obligation .claims
def bankObligation : Obligation Owner Value := obligation .bank

def baseline
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.LakehouseGatewayExample.model CedarPooSpec.LakehouseGatewayExample.schema × CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      (CedarPooSpec.LakehouseGatewayExample.program, CedarPooSpec.MultiAccountBankingExample.program)) : ProofObject Owner Value where
  state := fun
    | .claims =>
        (CedarPooSpec.LakehouseGatewayExample.decideAt (programContext := programContext.1)) "FailClosed"
          (CedarPooSpec.LakehouseGatewayExample.request
            CedarPooSpec.LakehouseGatewayExample.adjusterUS
            CedarPooSpec.LakehouseGatewayExample.queryClaims (some "US")) ==
          some .allow &&
        (CedarPooSpec.LakehouseGatewayExample.decideAt (programContext := programContext.1)) "FailClosed"
          (CedarPooSpec.LakehouseGatewayExample.request
            CedarPooSpec.LakehouseGatewayExample.adjusterUS
            CedarPooSpec.LakehouseGatewayExample.claimDetails (some "US")) ==
          some .allow
    | .bank =>
        (CedarPooSpec.MultiAccountBankingLineage.plannedRouteAllowed (programContext := programContext.2))
          "SourceM2M" "OwnerCombined"
  obligations := [claimsObligation, bankObligation]

theorem baselineCertificate : Certificate baseline := by
  intro candidate membership
  simp only [baseline, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with same | same
  · subst candidate
    change (CedarPooSpec.LakehouseGatewayExample.decideAt "FailClosed"
      (CedarPooSpec.LakehouseGatewayExample.request
        CedarPooSpec.LakehouseGatewayExample.adjusterUS
        CedarPooSpec.LakehouseGatewayExample.queryClaims (some "US")) ==
      some .allow &&
      CedarPooSpec.LakehouseGatewayExample.decideAt "FailClosed"
        (CedarPooSpec.LakehouseGatewayExample.request
          CedarPooSpec.LakehouseGatewayExample.adjusterUS
          CedarPooSpec.LakehouseGatewayExample.claimDetails (some "US")) ==
        some .allow) = true
    native_decide
  · subst candidate
    change CedarPooSpec.MultiAccountBankingLineage.plannedRouteAllowed
      "SourceM2M" "OwnerCombined" = true
    native_decide

/-- The patch value comes from the actual banking route under its incident
    overlay, rather than an invented Boolean flag. -/
def bankPause
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.MultiAccountBankingExample.model CedarPooSpec.MultiAccountBankingExample.schema :=
      CedarPooSpec.MultiAccountBankingExample.program) : Patch Owner Value :=
  Patch.set .bank
    ((CedarPooSpec.MultiAccountBankingLineage.plannedRouteAllowed (programContext := programContext))
      "SourceM2M" "TransferPaused")

theorem claimsUnaffected : unaffected claimsObligation bankPause := by
  intro key membership
  simp [claimsObligation, obligation] at membership
  subst key
  simp [bankPause, Patch.set]

theorem claimsCertificateReused :
    claimsObligation.holds (append baseline bankPause).state :=
  reuse baseline bankPause baselineCertificate claimsObligation
    (by simp [baseline]) claimsUnaffected

theorem bankCertificateInvalidated :
    ¬ bankObligation.holds (append baseline bankPause).state := by
  change CedarPooSpec.MultiAccountBankingLineage.plannedRouteAllowed
    "SourceM2M" "TransferPaused" ≠ true
  native_decide

end CedarPooSpec.AWS.ClaimSettlementRevision
