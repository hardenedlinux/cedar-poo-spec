import CedarPooSpec.Gateway.OAuthRefresh
import CedarPooSpec.Gateway.ZeroTrust

/-! Final OAuth use compares the inspected snapshot with the independently
read current commit. The Host authenticates the prefix and serializes this
check, replay reservation, and final effect with all revocation writers. -/
namespace CedarPooSpec.Gateway.OAuth.Revocation
open LeanPoo.Functional.DeclarativeMetadata

/-- The authority identity, commit position and exact committed ledger travel
together. Position equality alone does not establish snapshot identity. -/
structure Checkpoint where
  authorityId : String
  position : Nat
  ledger : Refresh.Ledger
  deriving DecidableEq

structure ReplicaRead where
  checked : Checkpoint
  replica : Checkpoint
  authority : Authority
  attempt : Attempt

structure FinalRead extends ReplicaRead where
  independent : Option Checkpoint

def check (input : FinalRead) : Option Authority :=
  if input.independent = some input.replica ∧ input.checked = input.replica then
    Refresh.useAccess input.replica.ledger input.authority input.attempt
  else none

def contract : Contract Unit FinalRead Authority where
  input := ⟨"checked-replica-and-independent-current-revocation-frontier", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"current-OAuth-admission-and-replay-reservation", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ input result => check input = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (input : FinalRead) : Except String (Authority × Unit) :=
  match check input with
  | some next => .ok (next, ())
  | none => .error "OAuth final use refused"

theorem accepted_retains_frontier (accepted : check input = some next) :
    input.independent = some input.replica ∧ input.checked = input.replica ∧
    Refresh.useAccess input.replica.ledger input.authority input.attempt = some next := by
  unfold check at accepted
  split at accepted
  · rename_i bound
    exact ⟨bound.1, bound.2, accepted⟩
  · contradiction

theorem different_replica_refused (input : FinalRead)
    (different : input.independent ≠ some input.replica) : check input = none := by
  simp [check, different]

theorem changed_after_check_refused (input : FinalRead)
    (changed : input.checked ≠ input.replica) : check input = none := by
  simp [check, changed]

/-- The Host authenticates an authority-owned committed prefix and its ledger
projection. It also attests the reservation at the actual effect boundary. -/
structure Readers (Effect View : Type) where
  readAt : Effect → View → ReplicaRead
  frontierAt : Effect → View → Option Checkpoint
  authentic : View → Checkpoint → Prop
  reservationCommitted : View → Authority → Prop

def Readers.observe (readers : Readers E V) (effect : E) (actual : V) : FinalRead :=
  ⟨readers.readAt effect actual, readers.frontierAt effect actual⟩

def Readers.mediates (readers : Readers E V) (effect : E) (actual : V) : Prop :=
  let input := readers.observe effect actual
  readers.authentic actual input.replica ∧
    ∃ receipt : Invocation contract prepare input,
      readers.reservationCommitted actual receipt.result

/-- Refine the existing Gateway FinalUse and continuing-use mediation slot.
All original admission, consumption and effect requirements remain in force. -/
def protect (host : Gateway.ZeroTrust.Host E V) (readers : Readers E V) :
    Gateway.ZeroTrust.Host E V :=
  { host with mediated := fun effect actual =>
      host.mediated effect actual ∧ readers.mediates effect actual }

theorem mediation_retains_original_and_frontier
    (admitted : (protect host readers).mediated effect actual) :
    let input := readers.observe effect actual
    host.mediated effect actual ∧ readers.authentic actual input.replica ∧
    input.independent = some input.replica ∧ input.checked = input.replica ∧
    ∃ next, Refresh.useAccess input.replica.ledger input.authority input.attempt = some next ∧
      readers.reservationCommitted actual next := by
  obtain ⟨original, authentic, receipt, installed⟩ := admitted
  have ⟨independent, checked, applied⟩ := accepted_retains_frontier receipt.logic
  exact ⟨original, authentic, independent, checked, receipt.result, applied, installed⟩

theorem no_mediation_without_current_check (readers : Readers E V)
    (refused : check (readers.observe effect actual) = none) :
    ¬ (protect host readers).mediated effect actual := by
  rintro ⟨_, _, receipt, _⟩
  have accepted := receipt.logic
  change check (readers.observe effect actual) = some receipt.result at accepted
  rw [refused] at accepted
  contradiction

theorem revoked_descendant_refused
    (framework : CedarPooSpec.ZeroTrust.Framework E Refresh.Ledger)
    (revocation : Invocation Refresh.revokeContract Refresh.prepareRevoke request)
    (pinned : input.independent = some frontier)
    (history : CedarPooSpec.ZeroTrust.Run framework (Refresh.LedgerStep E)
      revocation.result frontier.ledger)
    (linked : frontier.ledger.accessEntry input.attempt.grant.tokenHash = some entry)
    (family : entry.family = request.key) : check input = none := by
  cases accepted : check input with
  | none => rfl
  | some next =>
    have ⟨independent, _, access⟩ := accepted_retains_frontier accepted
    have same : input.replica = frontier := Option.some.inj (independent.symm.trans pinned)
    rw [same, Refresh.committed_descendant_blocks_access framework revocation history linked family] at access
    contradiction

section FinalUse
open Cedar.Spec
variable {E S V : Type} [BEq E] [LawfulBEq E] {project : E → S → Request}
  {original : Gateway.Profile} {object : Gateway.ProfileObject.Object}
  {publication : Gateway.ProfileObject.Publication original object}
  {prepared : Gateway.Prepared E S project} {model : PolicyModules.Model}
  {effect : E} {state : S} {context : Gateway.Context}
  {checks : List Gateway.Assessment} {entities : Entities}

theorem final_use_refused_without_current_check
    (host : Gateway.ZeroTrust.Host E V) (readers : Readers E V)
    (proposal : Gateway.ZeroTrust.Proposal (protect host readers) publication prepared model
      effect state context checks entities)
    (refused : check (readers.observe effect proposal.before) = none) :
    ¬ Nonempty (Gateway.ZeroTrust.FinalUse proposal) := by
  rintro ⟨use⟩
  have mediated := use.mediated
  rw [use.sameView] at mediated
  exact no_mediation_without_current_check readers refused mediated

end FinalUse

end CedarPooSpec.Gateway.OAuth.Revocation
