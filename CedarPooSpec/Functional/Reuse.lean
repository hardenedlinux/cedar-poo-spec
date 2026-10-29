import CedarPooSpec.Functional.Capabilities
import LeanPoo.Functional.ContextSlot

/-! One-root retention within an exact immutable Program. The underlying
LeanPOO ContextSlot owns storage, equality, replacement and factory alignment. -/
namespace CedarPooSpec.Functional
open Cedar.Spec
open LeanPoo.Functional

private abbrev RootValue (_program : Program model schema) (root : String) (_ : Unit) :=
  Except Error (Ready ⟨model, root, schema⟩)

/-- Reindex the complete prepared result onto root; model/schema and the exact
selected factory family remain captured by the Program index. The certificate
asserts exact outcome equality, including errors and publication behavior. -/
def Program.rootFamily (program : Program model schema) :
    @Requirements.Certified String Unit (RootValue program) [()]
      (fun root data => data.1 = program.at root) where
  factories := (program.at, PUnit.unit)
  valid := fun _ => rfl

abbrev RootSlot (program : Program model schema) :=
  Requirements.ContextSlot program.rootFamily

def RootSlot.empty (program : Program model schema) : RootSlot program :=
  Requirements.ContextSlot.empty program.rootFamily

def RootSlot.read {program : Program model schema} (slot : RootSlot program) (root : String) :
    Except Error (Ready ⟨model, root, schema⟩) × RootSlot program × Bool :=
  slot.consume (fun _ data _ => data.1) root

/-- Every hit or miss has the complete original outcome, not only equal policies. -/
theorem RootSlot.read_value {program : Program model schema} (slot : RootSlot program) (root : String) :
    (RootSlot.read slot root).1 = program.at root := by
  rw [RootSlot.read, Requirements.ContextSlot.consume_value]
  rfl

/-- An exact-root hit returns the retained result and unchanged slot. -/
theorem RootSlot.read_hit {program : Program model schema} (slot : RootSlot program)
    (root : String) (data : Requirements.Snapshot program.rootFamily root)
    (retained : slot.retained = some ⟨root, data⟩) :
    RootSlot.read slot root = (data.val.1, slot, true) := by
  unfold RootSlot.read Requirements.ContextSlot.consume
  rw [Requirements.ContextSlot.read_hit slot root data retained]

/-- Additional retained root outcomes are bounded independently of workload. -/
theorem RootSlot.bound {program : Program model schema} (slot : RootSlot program) : slot.retained.toList.length ≤ 1 := by
  cases slot.retained <;> simp

structure AuthorizationInput where
  name : String
  revision : String
  root : String
  request : Request
  entities : Entities

/-- Current request/entity rendering; no response or Host admission is retained. -/
def Program.authorizationCasesFrom (program : Program model schema) :
    List AuthorizationInput → RootSlot program → Except String (List Lean.Json)
  | [], _ => .ok []
  | input :: rest, slot => do
      let (result, next, _) := RootSlot.read slot input.root
      let ready ← result.mapError Error.message
      let row ← ready.authorizationCase input.name input.revision input.request input.entities
      let tail ← program.authorizationCasesFrom rest next
      return row :: tail

def Program.authorizationCases (program : Program model schema) (inputs : List AuthorizationInput) :
    Except String (List Lean.Json) :=
  program.authorizationCasesFrom inputs (RootSlot.empty program)

/-- Exact ordered values and first error for any initial slot and arbitrary inputs. -/
theorem Program.authorizationCasesFrom_eq (program : Program model schema)
    (inputs : List AuthorizationInput) (slot : RootSlot program) :
    program.authorizationCasesFrom inputs slot =
      Validation.traverse (fun input => program.authorizationCase input.name input.revision
        input.root input.request input.entities) inputs := by
  induction inputs generalizing slot with
  | nil => rfl
  | cons input rest ih =>
      simp only [authorizationCasesFrom, Validation.traverse, Program.authorizationCase,
        ih, RootSlot.read_value]
      cases (program.at input.root).mapError Error.message with
      | error error => rfl
      | ok ready =>
        cases ready.authorizationCase input.name input.revision input.request input.entities <;> rfl

theorem Program.authorizationCases_eq (program : Program model schema) (inputs : List AuthorizationInput) :
    program.authorizationCases inputs =
      Validation.traverse (fun input => program.authorizationCase input.name input.revision
        input.root input.request input.entities) inputs :=
  program.authorizationCasesFrom_eq inputs (RootSlot.empty program)

end CedarPooSpec.Functional
