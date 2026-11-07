import CedarPooSpec.AgenticAI.Commerce.Budget
import Init.Data.List.Perm

/-!
One-step scope attenuation and an exact chain of agent-to-agent delegations.
The Host authenticates each issuer and child mandate before setting `verified`.
The chain grants authority only; shared-budget reservation for child agents
requires a separately specified durable allocator.
-/

namespace CedarPooSpec.AgenticAI.Commerce

/-- A child can narrow the principal's merchant, product, amount, and time
    constraints, but cannot widen them or change the principal or asset. -/
def Mandate.attenuates (parent child : Mandate) : Bool :=
  parent.verified && child.verified &&
  !child.mandateId.isEmpty && !child.agentId.isEmpty &&
  !child.agentPublicKey.isEmpty &&
  child.mandateId != parent.mandateId && child.agentId != parent.agentId &&
  child.agentPublicKey != parent.agentPublicKey &&
  decide (child.principal = parent.principal) &&
  child.policyEpoch == parent.policyEpoch && child.asset == parent.asset &&
  !child.allowedMerchants.isEmpty && !child.allowedProducts.isEmpty &&
  child.allowedMerchants.all (parent.allowedMerchants.contains ·) &&
  child.allowedProducts.all (parent.allowedProducts.contains ·) &&
  child.perPurchaseCap <= parent.perPurchaseCap &&
  child.totalCap <= parent.totalCap && child.expiresAt <= parent.expiresAt

/-- `verified` asserts that the Host authenticated the parent agent's grant
    of this exact child mandate. Structural scope checking remains local. -/
structure Delegation where
  issuerAgentId : String
  parent : Mandate
  child : Mandate
  verified : Bool
  deriving DecidableEq, Repr

def Delegation.applies (step : Delegation)
    (parent : Mandate) : Bool :=
  step.verified && step.issuerAgentId == parent.agentId &&
  decide (step.parent = parent) && parent.attenuates step.child

/-- Every hop names the preceding mandate and uses identities and keys not
    already present in this exact chain. -/
private def Delegation.resolveWithSeen (current : Mandate)
    (seenMandates seenAgents seenKeys : List String) :
    List Delegation → Option Mandate
  | [] => some current
  | step :: rest =>
      if step.applies current &&
          !seenMandates.contains step.child.mandateId &&
          !seenAgents.contains step.child.agentId &&
          !seenKeys.contains step.child.agentPublicKey then
        resolveWithSeen step.child
          (step.child.mandateId :: seenMandates)
          (step.child.agentId :: seenAgents)
          (step.child.agentPublicKey :: seenKeys) rest
      else none

def Delegation.resolveChain (root : Mandate)
    (steps : List Delegation) : Option Mandate :=
  resolveWithSeen root [root.mandateId] [root.agentId] [root.agentPublicKey] steps

private theorem Delegation.resolveWithSeen_unique
    (steps : List Delegation) (current final : Mandate)
    (mandates agents keys : List String)
    (hm : mandates.Nodup) (ha : agents.Nodup) (hk : keys.Nodup)
    (resolved : resolveWithSeen current mandates agents keys steps = some final) :
    ((steps.map (·.child.mandateId)).reverse ++ mandates).Nodup ∧
    ((steps.map (·.child.agentId)).reverse ++ agents).Nodup ∧
    ((steps.map (·.child.agentPublicKey)).reverse ++ keys).Nodup := by
  induction steps generalizing current mandates agents keys with
  | nil => simpa using And.intro hm (And.intro ha hk)
  | cons step rest ih =>
    simp only [resolveWithSeen] at resolved
    split at resolved
    next admitted =>
      have fresh : step.child.mandateId ∉ mandates ∧
          step.child.agentId ∉ agents ∧ step.child.agentPublicKey ∉ keys := by
        have guards : ((step.applies current = true ∧
            step.child.mandateId ∉ mandates) ∧ step.child.agentId ∉ agents) ∧
            step.child.agentPublicKey ∉ keys := by
          simpa [List.contains_eq_mem] using admitted
        exact ⟨guards.1.1.2, guards.1.2, guards.2⟩
      have tail := ih step.child
        (step.child.mandateId :: mandates) (step.child.agentId :: agents)
        (step.child.agentPublicKey :: keys)
        (List.nodup_cons.mpr ⟨fresh.1, hm⟩)
        (List.nodup_cons.mpr ⟨fresh.2.1, ha⟩)
        (List.nodup_cons.mpr ⟨fresh.2.2, hk⟩) resolved
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using tail
    next => simp at resolved

/-- Pairwise signature/attenuation checks are insufficient: successful complete
resolution forbids reuse of any mandate, agent or holder key, at any depth. -/
theorem Delegation.resolvedLineageUnique
    (resolved : resolveChain root steps = some final) :
    (root.mandateId :: steps.map (·.child.mandateId)).Nodup ∧
    (root.agentId :: steps.map (·.child.agentId)).Nodup ∧
    (root.agentPublicKey :: steps.map (·.child.agentPublicKey)).Nodup := by
  have unique := resolveWithSeen_unique steps root final
    [root.mandateId] [root.agentId] [root.agentPublicKey]
    (by simp) (by simp) (by simp) resolved
  simp only [← List.reverse_cons] at unique
  exact ⟨unique.1.perm (List.reverse_perm _),
    unique.2.1.perm (List.reverse_perm _), unique.2.2.perm (List.reverse_perm _)⟩

end CedarPooSpec.AgenticAI.Commerce
