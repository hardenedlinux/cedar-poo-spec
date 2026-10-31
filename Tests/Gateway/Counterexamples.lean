import Tests.Gateway.Fixture

namespace CedarPooSpec.GatewayTest

private def initialResult := consume {} grants "approval"

-- These are expected counterexamples to stronger, unimplemented Host claims.
-- Both consumers of one pre-state succeed. Only a serialized durable CAS can
-- select one result; the pure library does not arbitrate concurrent callers.
#guard (consume {} grants "approval").isSome && (consume {} grants "approval").isSome
#guard (initialResult.bind fun _ => consume {} (grants "renewed") "renewed").isSome

-- A fresh approval cannot bypass the original key against the returned state.
#guard (initialResult.bind fun result =>
    consume result.operations (grants "renewed") "renewed").isNone

-- Provided metadata is not an authenticated canonical registry. A Host that
-- relabels all identities consistently can create a new family in this API.
def relabeledScope : Gateway.Scope :=
  { scope with
    claim := "other-claim"
    canonicalOperation := "other-operation"
    budgetDomain := "other-account"
    historyDomain := "other-history" }
def relabeledContext : Gateway.Context := { context with scope := relabeledScope }
def relabeledPrepared : Gateway.Prepared String Bool request :=
  { prepared with operationId := ⟨relabeledScope.canonicalOperation⟩, context := relabeledContext }
#guard (authorize relabeledPrepared (currentContext := relabeledContext)).isOk
#guard !(authorize relabeledPrepared (currentContext := context)).isOk

-- The original profile content is a Host commitment, not just its display ID.
def weakenedProfile : Gateway.Profile := { profile with requiredChecks := ["source"] }
#guard (authorize { prepared with profile := weakenedProfile }
    (assessments := [⟨"source", .satisfied⟩])).isOk

-- Names and satisfied labels alone do not prove real balances or true history.
#guard (let authoritativeRemainingBudget := 0
    authoritativeRemainingBudget == 0 && (authorize).isOk)
#guard !(authorize (currentContext := { context with historyRevision := 2 })).isOk
#guard (authorize (currentContext := context)).isOk
#guard !(authorize (currentContext := { context with policyRevision := 2 })).isOk

-- Equal policy bodies/zero pointwise Delta cannot compare distinct fact worlds.
#guard !(CedarPooSpec.Authorization.Delta.errorFreeAllow [permitPolicy]
    ⟨request "invoke" false, entities⟩)
#guard CedarPooSpec.Authorization.Delta.errorFreeAllow [permitPolicy]
    ⟨request "invoke" true, entities⟩

-- Fresh context at admission says nothing about a later epoch at dispatch.
#guard (authorize).isOk && (context.ownerEpoch != ({ context with ownerEpoch := 2 }).ownerEpoch)

-- The underlying general-purpose ledger only requires BEq. Gateway strengthens
-- its interface to LawfulBEq, so a custom comparator cannot identify distinct
-- effects. This counterexample uses only the weaker underlying interface.
private inductive UnlawfulEffect where
  | invoke | tool
private instance : BEq UnlawfulEffect := ⟨fun _ _ => true⟩
#guard (Admission.AuthorityLedger.consume
    (⟨[⟨"approval", UnlawfulEffect.invoke, 1, 0⟩]⟩ : Admission.AuthorityLedger UnlawfulEffect)
    "approval" UnlawfulEffect.tool).isOk

end CedarPooSpec.GatewayTest
