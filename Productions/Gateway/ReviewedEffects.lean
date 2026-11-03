import CedarPooSpec.Gateway.ReviewedEffect
import CedarPooSpec.SchemaJson
import CedarPooSpec.Transport.SourceCatalog
import CedarPooSpec.Functional.Capabilities

/-! Shared nonidentity review workload over original proof-bound C4 sources.
No Example, transport client, solver replacement or fabricated review is imported. -/
namespace CedarPooSpec.Production.ReviewedEffects
open Cedar.Spec Cedar.Validation CedarPooSpec

structure Plan where
  model : PolicyModules.Model
  schema : Transport.SchemaSource
  beforeRoot : String
  heldLeft : String
  heldRight : String
  heldRoot : String
  restoredLeft : String
  restoredRight : String
  restoredRoot : String

private def fresh (taken : List String) (stem : String) : String :=
  ((List.range (taken.length + 1)).map (fun n => stem ++ toString n)).find?
    (fun name => !taken.contains name) |>.getD stem

/-- Extend the original declarations rather than flattening the source policies.
The four roots on each leg are actual C4 compositions. -/
def plan (source : Transport.PolicySource) (schema : Transport.SchemaSource) : Except String Plan := do
  let some origin := source.origin | throw "missing proof-bound C4 origin"
  let names := origin.model.modules.map (·.name)
  let a := fresh names "cedar-held-left-"
  let b := fresh (a :: names) "cedar-held-right-"
  let c := fresh (b :: a :: names) "cedar-held-"
  let d := fresh (c :: b :: a :: names) "cedar-restored-left-"
  let e := fresh (d :: c :: b :: a :: names) "cedar-restored-right-"
  let f := fresh (e :: d :: c :: b :: a :: names) "cedar-restored-"
  let holdId := fresh (source.policies.map (·.id)) "cedar-review-hold-"
  let hold : Policy := {
    id := holdId
    effect := .forbid
    principalScope := .principalScope .any
    actionScope := .actionScope .any
    resourceScope := .resourceScope .any
    condition := [] }
  let model : PolicyModules.Model := { modules := origin.model.modules ++ [
    { name := a, parentOrders := [[origin.root]], edits := [.extend hold] },
    { name := b, parentOrders := [[origin.root]] },
    { name := c, parentOrders := [[a,b]] },
    { name := d, parentOrders := [[c]], edits := [.remove holdId] },
    { name := e, parentOrders := [[c]] },
    { name := f, parentOrders := [[d,e]] }] }
  return ⟨model, schema, origin.root, a,b,c,d,e,f⟩

private def policyEditJson (kind : String) (policy : Policy) : Except String Lean.Json := do
  return Lean.Json.mkObj [("kind", Lean.toJson kind), ("id", Lean.toJson policy.id),
    ("policy", ← (PolicyJson.policy policy).mapError reprStr)]
private def editJson : PolicyModules.Edit → Except String Lean.Json
  | .remove id => .ok (Lean.Json.mkObj [("kind", Lean.toJson "remove"), ("id", Lean.toJson id)])
  | .extend policy => policyEditJson "extend" policy
  | .overlay policy => policyEditJson "overlay" policy

def modelJson (plan : Plan) : Except String Lean.Json := do
  return Lean.toJson (← plan.model.modules.mapM fun module => do
    return Lean.Json.mkObj [("name", Lean.toJson module.name),
      ("parents", Lean.toJson module.parentOrders), ("suffix", Lean.toJson module.suffix),
      ("edits", Lean.toJson (← module.edits.mapM editJson))])

private def casesAt (plan : Plan) (rows : List Transport.Case) (root : String) :
    Except String Transport.Manifest := do
  let program ← (Functional.prepareProgram Functional.standard plan.model plan.schema.meaning [root]).mapError Functional.Error.message
  let cases ← rows.mapM fun row => program.case row.name row.revision root row.request row.entities
  return ⟨cases, some plan.schema⟩

/-- The existing analyzer captures exact declarations, schema and epoch. -/
def capture (plan : Plan) (restoring : Bool) : IO Authorization.Delta.ReviewedInteraction := do
  let (base,left,right,combined,epoch) := if restoring then
    (plan.heldRoot,plan.restoredLeft,plan.restoredRight,plan.restoredRoot,8)
    else (plan.beforeRoot,plan.heldLeft,plan.heldRight,plan.heldRoot,7)
  IO.ofExcept ((← Authorization.Delta.analyzeAndCapture plan.model base left right combined
    plan.schema.meaning epoch).mapError reprStr)

private def analysisName (reviewed : Authorization.Delta.ReviewedInteraction) : String :=
  match reviewed.analysis.outcome with
  | .noCombinedGain => "noGain" | .branchExpanded => "branchGain" | .jointOnlyGain _ => "jointGain"

private def reviewJson (plan : Plan) (reviewed : Authorization.Delta.ReviewedInteraction) :
    IO Lean.Json := do
  let policies := reviewed.snapshot.base.policies
  let active : Authorization.Delta.ReleaseState :=
    ⟨reviewed.snapshot.base.root, policies, .enforcing, reviewed.snapshot.epoch⟩
  let before ← IO.ofExcept ((PolicyJson.policySet policies).mapError reprStr)
  let after ← IO.ofExcept ((PolicyJson.policySet reviewed.snapshot.combined.policies).mapError reprStr)
  let mut witnesses : Array Lean.Json := #[]
  let program ← IO.ofExcept ((Functional.prepareProgram Functional.standard plan.model plan.schema.meaning
    [reviewed.snapshot.base.root, reviewed.snapshot.combined.root]).mapError Functional.Error.message)
  for gain in reviewed.analysis.combined.symbolic.expansions do
    let before ← IO.ofExcept (program.case "delta-witness" "before" reviewed.snapshot.base.root
      gain.witness.request gain.witness.entities)
    let after ← IO.ofExcept (program.case "delta-witness" "after" reviewed.snapshot.combined.root
      gain.witness.request gain.witness.entities)
    witnesses := witnesses.push (Lean.Json.mkObj [("before", ← IO.ofExcept before.toJson),
      ("after", ← IO.ofExcept after.toJson)])
  return Lean.Json.mkObj [("epoch", Lean.toJson reviewed.snapshot.epoch),
    ("before_root", Lean.toJson reviewed.snapshot.base.root),
    ("after_root", Lean.toJson reviewed.snapshot.combined.root),
    ("before", before), ("after", after), ("analysis", Lean.toJson (analysisName reviewed)),
    ("environments_checked", Lean.toJson reviewed.analysis.combined.symbolic.environmentsChecked),
    ("witnesses", Lean.toJson witnesses),
    ("without_approval", Lean.toJson (Gateway.ReviewedEffect.invoke reviewed plan.model plan.schema.meaning active false).isOk),
    ("with_approval", Lean.toJson (Gateway.ReviewedEffect.invoke reviewed plan.model plan.schema.meaning active true).isOk)]

def project (plan : Plan) (rows : List Transport.Case) : IO Lean.Json := do
  IO.eprintln s!"REVIEW-ANALYZE: {plan.beforeRoot}; cases={rows.length}"
  let held ← capture plan false
  let restored ← capture plan true
  let before ← IO.ofExcept (casesAt plan rows plan.beforeRoot)
  let middle ← IO.ofExcept (casesAt plan rows plan.heldRoot)
  let after ← IO.ofExcept (casesAt plan rows plan.restoredRoot)
  let stages ← IO.ofExcept (Transport.sourceCatalog [("before", .manifest before),
    ("held", .manifest middle), ("restored", .manifest after)])
  return Lean.Json.mkObj [("model", ← IO.ofExcept (modelJson plan)),
    ("schema", plan.schema.value), ("initial_root", Lean.toJson plan.beforeRoot),
    ("stages", stages), ("reviews", Lean.toJson [← reviewJson plan held, ← reviewJson plan restored]),
    ("expected_effects", Lean.toJson (after.cases.map fun row =>
      Gateway.EffectProtocol.Outcome.toJson (Gateway.EffectProtocol.Outcome.resolve
        (row.response.get.decision == .allow && row.response.get.erroringPolicies.isEmpty) true false)))]
end CedarPooSpec.Production.ReviewedEffects
