import CedarPooSpec.PolicyModules

/-!
One banking line-of-business owner grants a selected set of Gateway actions.
The action catalog, customer identities, token exchange, and data-plane
authorization belong to the consuming bank and platform deployment.
-/

namespace CedarPooSpec.Vertical.FinancialServices

open Cedar.Spec CedarPooSpec.PolicyModules

structure BankingToolOwner where
  policyId : PolicyID
  principalType : EntityType
  gateway : EntityUID
  actions : List EntityUID
  deriving DecidableEq

def BankingToolOwner.policy (owner : BankingToolOwner) : Policy :=
  { id := owner.policyId, effect := .permit,
    principalScope := .principalScope (.is owner.principalType),
    actionScope := .actionInAny owner.actions,
    resourceScope := .resourceScope (.eq owner.gateway),
    condition := [] }

def BankingToolOwner.introduce (owner : BankingToolOwner) : Edit :=
  .extend owner.policy

def BankingToolOwner.revise (owner : BankingToolOwner) : Edit :=
  .overlay owner.policy

def BankingToolOwner.withdraw (owner : BankingToolOwner) : Edit :=
  .remove owner.policyId

end CedarPooSpec.Vertical.FinancialServices
