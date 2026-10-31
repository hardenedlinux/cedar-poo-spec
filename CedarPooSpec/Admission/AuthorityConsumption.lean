import Lean.Data.Json

/-!
A pure, typed model of consumption for a Host-owned authorization instance.
The Host must authenticate grants and persist the ledger transactionally.
-/

namespace CedarPooSpec.Admission

structure AuthorityGrant (Effect : Type) where
  id : String
  effect : Effect
  maxUses : Nat
  used : Nat := 0
  deriving BEq, Repr

structure AuthorityLedger (Effect : Type) where
  grants : List (AuthorityGrant Effect) := []
  deriving BEq, Repr

namespace AuthorityLedger

inductive Error where
  | missing
  | duplicate
  | effectMismatch
  | exhausted
  deriving BEq, Repr

/-- A stable authorization-instance ID is unique in the Host ledger and
    binds the exact effect. The use limit is read from the ledger, never from
    a prepared ticket. -/
def check [BEq Effect] (ledger : AuthorityLedger Effect) (id : String)
    (effect : Effect) : Except Error Unit :=
  match ledger.grants.filter (fun grant => grant.id == id) with
  | [] => .error .missing
  | [grant] =>
      if grant.effect != effect then .error .effectMismatch
      else if grant.used >= grant.maxUses then .error .exhausted
      else .ok ()
  | _ => .error .duplicate

/-- Pure state transition. A production Host must commit the new ledger and
    the associated effect reservation under one serialized transaction. -/
def consume [BEq Effect] (ledger : AuthorityLedger Effect) (id : String)
    (effect : Effect) : Except Error (AuthorityLedger Effect) := do
  check ledger id effect
  pure { grants := ledger.grants.map fun grant =>
    if grant.id == id then { grant with used := grant.used + 1 } else grant }

end AuthorityLedger
end CedarPooSpec.Admission
