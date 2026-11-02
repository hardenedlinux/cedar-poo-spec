import CedarPooSpec.Functional.ObjectProfile

/-! Native workload inputs; actual admission and projection remain shared. -/
namespace CedarPooSpec.FunctionalProfileWorkloads
open LeanPoo CedarPooSpec.Functional.ObjectProfile

structure Probe where
  name : String
  guards : Bool
  fields : Nat
  consume : Nat → String → Bool → Except String Nat

/-- Fresh construction is inside the measured operation, so closed fixture
expressions cannot be precomputed while building a benchmark closure. -/
@[noinline] def consume {Key : Type} {Value : Key → Type} [DecidableEq Key] [BEq Key]
    [LawfulBEq Key] [Hashable Key] (contract : Check Key Value)
    (profile : Object Key Value) (key : Key) (forged : Value key)
    (iteration : Nat) (mode : String) (reuse : Bool) : Except String Nat :=
  ( (if mode == "missing" then LeanPoo.Object.Dataflow.define s!"Missing{iteration}" (pure ⟨⟩)
    else profile.extendWith s!"Current{iteration}" do
      if mode == "forged" then LeanPoo.Object.Dataflow.Builder.value key forged else pure ⟨⟩)
    |>.mapError (fun _ => "profile construction failed")).bind fun current => do
  let keys := LeanPoo.allSlots profile.plan
  if reuse then
    match Session.open contract (factory contract) current with
    | .error _ => return 0
    | .ok access => return keys.foldl (fun count key => count + if (access.read key).isSome then 1 else 0) 0
  else return keys.foldl (fun count key => count + if (read contract current key).isSome then 1 else 0) 0

/-- Fixed sizes; force each result before stopping its clock. -/
def run (probe : Probe) : IO Unit := do
  for mode in ["valid", "forged", "missing"] do
    for sample in [1, 2, 3] do
      let mut coldNs := 0
      let mut sharedNs := 0
      let mut coldAlloc := 0
      let mut sharedAlloc := 0
      let mut checksum := 0
      for iteration in List.range 128 do
        let expected := if mode == "valid" then probe.fields else 0
        let alloc ← IO.getNumHeartbeats
        let started ← IO.monoNanosNow
        let cold ← IO.ofExcept (probe.consume iteration mode false)
        unless cold == expected do throw (IO.userError s!"cold profile mismatch: {probe.name}/{mode}")
        coldNs := coldNs + ((← IO.monoNanosNow) - started)
        coldAlloc := coldAlloc + ((← IO.getNumHeartbeats) - alloc)
        let alloc ← IO.getNumHeartbeats
        let started ← IO.monoNanosNow
        let shared ← IO.ofExcept (probe.consume iteration mode true)
        unless shared == cold do throw (IO.userError s!"profile batch/refusal mismatch: {probe.name}/{mode}")
        sharedNs := sharedNs + ((← IO.monoNanosNow) - started)
        sharedAlloc := sharedAlloc + ((← IO.getNumHeartbeats) - alloc)
        checksum := checksum + shared
      IO.println s!"PROFILE-PREP name={probe.name} mode={mode} sample={sample} iterations=128 fields={probe.fields} cold_ns={coldNs} shared_ns={sharedNs} cold_small_allocation_heartbeats={coldAlloc} shared_small_allocation_heartbeats={sharedAlloc} checksum={checksum}"
      IO.println s!"measurement: profile.{probe.name}.{mode}.cold.sample{sample} {coldNs} ns"
      IO.println s!"measurement: profile.{probe.name}.{mode}.shared.sample{sample} {sharedNs} ns"
end CedarPooSpec.FunctionalProfileWorkloads
