import CedarPooSpec.Governance.ScopedApproval

/-!
A human-to-Agent delegation is narrower than the human's own membership.
The Host authenticates the grant and its revision; this value is only a
scope check and is never evidence of a signature by itself.
-/

namespace CedarPooSpec.Governance.Personnel

open Cedar.Spec

structure Delegation where
  id : String
  origin : EntityUID
  agent : EntityUID
  action : EntityUID
  asset : EntityUID
  destination : EntityUID
  purpose : String
  revision : Nat
  expiresAt : Nat
  deriving BEq, DecidableEq

def Delegation.applies (grant : Delegation)
    (origin agent action asset destination : EntityUID)
    (purpose : String) (revision now : Nat) : Bool :=
  grant.origin == origin && grant.agent == agent &&
  grant.action == action && grant.asset == asset &&
  grant.destination == destination && grant.purpose == purpose &&
  grant.revision == revision && decide (now < grant.expiresAt)

end CedarPooSpec.Governance.Personnel
