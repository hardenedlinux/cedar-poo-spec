import CedarPooSpec.Functional.Reuse
import Examples.Enterprise.Agent.Fanout.CrossAgentEgress

/-! Fixed local Lean-run probe. Timings are observations, not admission thresholds. -/
namespace CedarPooSpec.FunctionalReuseBenchmark
open Cedar.Spec CedarPooSpec.Functional CedarPooSpec.CrossAgentEgressExample

def cold : Program model schema :=
  (prepareProgram standard model schema []).toOption.get (by native_decide)

@[noinline] def observe (ready : Ready ⟨model, root, schema⟩) (iteration : Nat) : Nat :=
  let state : State := { budget := { sharedUsed := Int64.ofNat (iteration % 2) } }
  let allowed := (ready.authorize [request .delegationShared state sendA] entities).allowed
  ready.checked.policies.length + if allowed then 1 else 0

@[noinline] def read (source : Program model schema) (root : String) (iteration : Nat) : Except CedarPooSpec.Functional.Error Nat := do
  return observe (← source.at root) iteration

def measure (source : Program model schema) (rootAt : Nat → String) (count : Nat) : IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for index in List.range count do
    match read source (rootAt index) index with
    | .error error => throw (IO.userError error.message)
    | .ok value => checksum := checksum + value
  return ((← IO.monoNanosNow) - start, checksum)

def measureSlot (rootAt : Nat → String) (count : Nat) : IO (Nat × Nat × Nat) := do
  let start ← IO.monoNanosNow
  let mut slot := RootSlot.empty cold
  let mut checksum := 0
  let mut hits := 0
  for index in List.range count do
    let (result, next, reused) := RootSlot.read slot (rootAt index)
    slot := next
    if reused then hits := hits + 1
    match result with
    | .error error => throw (IO.userError error.message)
    | .ok ready => checksum := checksum + observe ready index
  return ((← IO.monoNanosNow) - start, checksum, hits)

def main (args : List String) : IO Unit := do
  let root := args.headD "CrossAgentGoverned"
  for (label, rootAt) in [("hot", fun (_ : Nat) => root),
      ("churn", fun index => if index % 2 == 0 then root else "CrossAgentIncident")] do
    discard <| measure cold rootAt 16
    discard <| measure program rootAt 16
    discard <| measureSlot rootAt 16
    for sample in [1, 2, 3] do
      let baseline ← measure cold rootAt 128
      let retained ← measure program rootAt 128
      let slotted ← measureSlot rootAt 128
      unless baseline.2 == retained.2 && baseline.2 == slotted.2.1 do
        throw (IO.userError "Functional reuse checksum mismatch")
      unless slotted.2.2 == (if label == "hot" then 127 else 0) do
        throw (IO.userError "Functional reuse hit/miss mismatch")
      IO.println s!"scenario={label} sample={sample} reads=128 cold_ns={baseline.1} all_roots_ns={retained.1} slot_ns={slotted.1} hits={slotted.2.2} retained_bound=1 checksum={baseline.2}"
end CedarPooSpec.FunctionalReuseBenchmark

def main (args : List String) : IO Unit := CedarPooSpec.FunctionalReuseBenchmark.main args
