import CedarPooSpec.AgenticAI.Commerce.Budget
import CedarPooSpec.AgenticAI.Commerce.Consumption
import Lean.Data.Json

/-!
JSON claims shared with the optional Rust `agentic-ai-commerce-projection` API.
They deliberately omit `verified`: only a trusted Host may set that flag after
comparing these fields with live Rust `VerifiedMandate` / `VerifiedOffer` values
and checking current time, key status, policy, and revocation state.
-/

namespace CedarPooSpec.AgenticAI.Commerce

private def object (fields : List (String × Lean.Json)) : Lean.Json :=
  Lean.Json.mkObj fields

/-- Serialize every mandate field except the Host-owned `verified` bit. -/
def Mandate.claimsJson (mandate : Mandate) : Lean.Json :=
  object [
    ("mandateId", Lean.toJson mandate.mandateId),
    ("principal", object [
      ("ty", object [
        ("id", Lean.toJson mandate.principal.ty.id),
        ("path", Lean.toJson mandate.principal.ty.path)]),
      ("eid", Lean.toJson mandate.principal.eid)]),
    ("agentId", Lean.toJson mandate.agentId),
    ("agentPublicKey", Lean.toJson mandate.agentPublicKey),
    ("allowedMerchants", Lean.toJson mandate.allowedMerchants),
    ("allowedProducts", Lean.toJson mandate.allowedProducts),
    ("asset", Lean.toJson mandate.asset),
    ("perPurchaseCap", Lean.toJson mandate.perPurchaseCap),
    ("totalCap", Lean.toJson mandate.totalCap),
    ("policyEpoch", Lean.toJson mandate.policyEpoch),
    ("expiresAt", Lean.toJson mandate.expiresAt)]

/-- The exact terms retained by offers, purchases and shared reservations. -/
def PurchaseTerms.claimsJson (terms : PurchaseTerms) : Lean.Json :=
  object [
    ("merchantId", Lean.toJson terms.merchantId),
    ("productId", Lean.toJson terms.productId),
    ("offerId", Lean.toJson terms.offerId),
    ("checkoutCommitment", Lean.toJson terms.checkoutCommitment),
    ("amountMinor", Lean.toJson terms.amountMinor),
    ("asset", Lean.toJson terms.asset)]

/-- Serialize every merchant-offer field except the Host-owned `verified` bit. -/
def MerchantOffer.claimsJson (offer : MerchantOffer) : Lean.Json :=
  object [
    ("terms", offer.terms.claimsJson),
    ("expiresAt", Lean.toJson offer.expiresAt)]

def Purchase.claimsJson (purchase : Purchase) : Lean.Json :=
  object [
    ("purchaseId", Lean.toJson purchase.purchaseId),
    ("mandateId", Lean.toJson purchase.mandateId),
    ("agentId", Lean.toJson purchase.agentId),
    ("terms", purchase.terms.claimsJson)]

/-- Persisted claims carry no reusable verification flags. The Host authenticates
    the current head and rechecks authority before any later reservation. -/
def SharedBudget.claimsJson (state : SharedBudget) : Lean.Json :=
  object [
    ("root", state.root.claimsJson),
    ("now", Lean.toJson state.now),
    ("reservations", Lean.toJson (state.reservations.map (fun entry => object [
      ("lineage", Lean.toJson (entry.lineage.map (·.claimsJson))),
      ("purchase", entry.purchase.claimsJson)]))),
    ("revokedMandateIds", Lean.toJson state.revokedMandateIds),
    ("revision", Lean.toJson state.revision)]

/-- Credential projection omits both issuer and commit verification flags. -/
def Credential.claimsJson (credential : Credential) : Lean.Json :=
  let receipt := credential.receipt
  object [
    ("credentialId", Lean.toJson credential.credentialId),
    ("issuerId", Lean.toJson credential.issuerId),
    ("expiresAt", Lean.toJson credential.expiresAt),
    ("receipt", object [
      ("scope", Lean.toJson receipt.scope),
      ("operationId", Lean.toJson receipt.operationId),
      ("expectedRevision", Lean.toJson receipt.expectedRevision),
      ("expectedContentId", Lean.toJson receipt.expectedContentId),
      ("committedRevision", Lean.toJson receipt.committedRevision),
      ("committedContentId", Lean.toJson receipt.committedContentId),
      ("reservation", object [
        ("lineage", Lean.toJson (receipt.reservation.lineage.map (·.claimsJson))),
        ("purchase", receipt.reservation.purchase.claimsJson)])])]

def PaymentDispatch.claimsJson (request : PaymentDispatch) : Lean.Json :=
  object [("providerId", Lean.toJson request.providerId),
    ("idempotencyKey", Lean.toJson request.idempotencyKey),
    ("credential", request.credential.claimsJson),
    ("authority", object [
      ("root", object [("budgetScope", Lean.toJson request.authority.root.budgetScope),
        ("mandateId", Lean.toJson request.authority.root.mandateId)]),
      ("generation", Lean.toJson request.authority.generation),
      ("retired", Lean.toJson request.authority.retired)])]

def ConsumptionLedger.claimsJson (state : ConsumptionLedger) : Lean.Json :=
  object [("budgetScope", Lean.toJson state.budgetScope),
    ("revision", Lean.toJson state.revision),
    ("requests", Lean.toJson (state.requests.map (·.claimsJson)))]

end CedarPooSpec.AgenticAI.Commerce
