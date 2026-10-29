import Cedar.Spec.Policy
import LeanPoo.Object.Definition
import LeanPoo.Object.Debug
import LeanPoo.Compose

/-!
C4 composes policy-producing modules. Edit intent is explicit; the result is
an ordinary Cedar policy set, and Cedar still owns permit/forbid aggregation.
-/

namespace CedarPooSpec.PolicyModules

open Cedar.Spec

inductive Edit where
  | extend (policy : Policy)
  | overlay (policy : Policy)
  | remove (policyId : PolicyID)
  deriving DecidableEq

def Edit.policyId : Edit → PolicyID
  | .extend policy | .overlay policy => policy.id
  | .remove id => id

/-- Lift a generated policy family into explicit POO edits. -/
def Edit.extendAll (policies : Policies) : List Edit :=
  policies.map Edit.extend

def Edit.overlayAll (policies : Policies) : List Edit :=
  policies.map Edit.overlay

structure Module where
  name : String
  parentOrders : List (List String) := []
  suffix : Bool := false
  edits : List Edit := []
  deriving DecidableEq

def Module.node (module : Module) : LeanPoo.C4.Node :=
  { name := module.name, parentOrders := module.parentOrders,
    suffix := module.suffix }

inductive Built where
  | schema (source : List Module)
      (value : LeanPoo.Object.Schema PolicyID (fun _ => Option Policy))
  | object (source : List Module)
      (value : LeanPoo.Object.Memoized PolicyID (fun _ => Option Policy))

structure Model where
  modules : List Module
  built : Option Built := none

private def Built.source : Built → List Module
  | .schema source _ | .object source _ => source

private def Built.toSchema : Built →
    LeanPoo.Object.Schema PolicyID (fun _ => Option Policy)
  | .schema _ cached => cached
  | .object _ cached => cached.plan.schema

/-- One source-identity gate for every retained schema, plan and object view. -/
private def Model.activeBuilt? (model : Model) : Option Built :=
  model.built.filter fun built => built.source == model.modules

private def Model.activeSchema? (model : Model) :
    Option (LeanPoo.Object.Schema PolicyID (fun _ => Option Policy)) :=
  model.activeBuilt?.map Built.toSchema

/-- Return the active first-class object only while its source modules match. -/
def Model.currentObject? (model : Model) :
    Option (LeanPoo.Object.Memoized PolicyID (fun _ => Option Policy)) :=
  match model.activeBuilt? with
  | some (.object _ object) => some object
  | _ => none

def Model.graph (model : Model) : LeanPoo.C4.Graph :=
  match model.activeSchema? with
  | some schema => schema.graph
  | none => { nodes := model.modules.map Module.node }

/-- Policy IDs are typed object slots. Each direct edit writes the slot body;
    removal writes an explicit tombstone. Edit validation stays Cedar-specific. -/
private def Module.program (module : Module) :
    LeanPoo.Object.Declaration.Builder PolicyID (fun _ => Option Policy) PUnit := do
    for edit in module.edits do
      match edit with
      | .extend policy | .overlay policy =>
          LeanPoo.Object.Declaration.Builder.value policy.id (some policy)
      | .remove id =>
          LeanPoo.Object.Declaration.Builder.value id none

private def Module.declaration (module : Module) :
    LeanPoo.Object.Declaration PolicyID (fun _ => Option Policy) :=
  LeanPoo.Object.Declaration.build module.program

/-- Create one policy owner as a first-class LeanPOO object. -/
def Model.define (name : String) (edits : List Edit := []) :
    Except LeanPoo.C4.Error Model := do
  let module : Module := { name, edits }
  let object ← LeanPoo.Object.define name module.program
  let modules := [module]
  return { modules, built := some (.object modules object) }

private def Model.schema (model : Model) :
    LeanPoo.Object.Schema PolicyID (fun _ => Option Policy) :=
  match model.activeSchema? with
  | some schema => schema
  | none =>
      { graph := model.graph
        declaration := fun name =>
          (model.modules.find? (fun module => module.name == name)).map
            Module.declaration }

private def Model.planAt (model : Model) (root : String) :
    Except LeanPoo.C4.Error
      (LeanPoo.Object.Plan PolicyID (fun _ => Option Policy)) := do
  if let some object := model.currentObject? then
    if object.plan.root == root then return object.plan
  LeanPoo.Object.compile model.schema root

/-- Obtain a first-class object for any valid root in this policy family.
    This is a composition view; publish through Cedar validation instead. -/
def Model.objectAt (model : Model) (root : String) :
    Except LeanPoo.C4.Error
      (LeanPoo.Object.Memoized PolicyID (fun _ => Option Policy)) := do
  if let some object := model.currentObject? then
    if object.plan.root == root then return object
  let plan ← model.planAt root
  return plan.memoize

/-- Inspect C4 resolution even if the Cedar edit sequence is invalid. -/
def Model.explainResolution (model : Model) (root : String) (id : PolicyID) :
    Except LeanPoo.C4.Error (LeanPoo.Object.Debug.Resolution PolicyID) := do
  let plan ← model.planAt root
  return LeanPoo.Object.Debug.Plan.explain plan id

/-- Stage a single-parent policy owner through LeanPOO's extension API.
    The final mix or publication compiles the complete C4 topology. -/
def Model.extend (model : Model) (name parent : String)
    (edits : List Edit := []) : Except LeanPoo.C4.Error Model := do
  let module : Module := { name, parentOrders := [[parent]], edits }
  if let some receiver := model.currentObject? then
    if receiver.plan.root == parent then
      let object ← receiver.extendWith name module.program
      let modules := model.modules ++ [module]
      return { modules, built := some (.object modules object) }
  let schema ← LeanPoo.extendSchema model.schema name parent module.declaration
  let modules := model.modules ++ [module]
  return { modules, built := some (.schema modules schema) }

/-- Compose ordered policy owners through LeanPOO's C4 mix operation. -/
def Model.mix (model : Model) (name : String) (supers : List String)
    (edits : List Edit := []) : Except LeanPoo.C4.Error Model := do
  let module : Module := { name, parentOrders := if supers.isEmpty then [] else [supers], edits }
  let object ← match model.currentObject? with
    | some receiver => receiver.defineNodeWith module.node module.program
    | none => LeanPoo.Object.defineNodeIn model.schema module.node module.program
  let modules := model.modules ++ [module]
  return { modules, built := some (.object modules object) }

/-- Compose independently built policy-owner families by their selected roots.
    LeanPOO rejects overlapping node names; Cedar still validates edit intent
    and authorization when the combined root is compiled or published. -/
def Model.combine (first : Model) (firstRoot : String)
    (others : List (Model × String)) (name : String)
    (edits : List Edit := []) :
    Except LeanPoo.Object.CombineError Model := do
  let receiver ← (first.objectAt firstRoot).mapError .c4
  let parents ← others.mapM fun (model, root) =>
    (model.objectAt root).mapError .c4
  let module : Module :=
    { name, parentOrders := [firstRoot :: others.map Prod.snd], edits }
  let object ← receiver.defineFrom name parents module.program
  let modules := first.modules ++ others.flatMap (·.1.modules) ++ [module]
  return { modules, built := some (.object modules object) }

/-- Inspect the C4-composed policy slots before Cedar edit validation.
    Publication must still go through `compile` or `compileWithTrace`. -/
def Model.compilePlan (model : Model) (root : String) :
    Except LeanPoo.C4.Error
      (LeanPoo.Object.CompiledPlan PolicyID (fun _ => Option Policy)) := do
  let plan ← model.planAt root
  return plan.compileMemo

inductive Error where
  | c4 (error : LeanPoo.C4.Error)
  | missingModule (name : String)
  | policyAlreadyExists (id : PolicyID)
  | missingPolicy (id : PolicyID)
  | competingEdits (id previousOwner currentOwner : String)
  | inconsistentResolution (id : PolicyID)
  | duplicateInputIds (side : String)
  | unrepresentableOrder
  deriving Repr, BEq

/-- A surviving policy and the modules responsible for its origin and latest edit. -/
structure CompiledPolicy where
  policy : Policy
  introducedBy : String
  lastEditedBy : String

structure AppliedEdit where
  moduleName : String
  edit : Edit

structure Compilation where
  policies : List CompiledPolicy
  applied : List AppliedEdit

/-- C4 declaration chain together with the Cedar-validated policy and edits. -/
structure PolicyExplanation where
  resolution : LeanPoo.Object.Debug.Resolution PolicyID
  effective : Option CompiledPolicy
  applied : List AppliedEdit

private structure PolicyOrigin where
  id : PolicyID
  introducedBy : String
  lastEditedBy : String

private def applyEdit (owner : String) (ancestors : List String)
    (current : List PolicyOrigin) : Edit → Except Error (List PolicyOrigin)
  | .extend policy =>
      if current.any (fun entry => entry.id == policy.id) then
        .error (.policyAlreadyExists policy.id)
      else
        let entry : PolicyOrigin :=
          { id := policy.id, introducedBy := owner, lastEditedBy := owner }
        .ok (current ++ [entry])
  | .overlay policy => do
      let some previous := current.find? (fun entry => entry.id == policy.id)
        | throw (.missingPolicy policy.id)
      if !ancestors.contains previous.lastEditedBy then
        throw (.competingEdits policy.id previous.lastEditedBy owner)
      return current.map fun entry =>
        if entry.id == policy.id then
          { entry with lastEditedBy := owner }
        else entry
  | .remove id => do
      let some previous := current.find? (fun entry => entry.id == id)
        | throw (.missingPolicy id)
      if !ancestors.contains previous.lastEditedBy then
        throw (.competingEdits id previous.lastEditedBy owner)
      return current.filter (fun entry => entry.id != id)

/-- Share the compiled C4 plan with diagnostics without resolving the graph
    a second time. Cedar's fold retains edit intent, order, and provenance. -/
private def Model.compileWithPlan (model : Model) (root : String) :
    Except Error
      (LeanPoo.Object.CompiledPlan PolicyID (fun _ => Option Policy) × Compilation) := do
  let compiled ← (model.compilePlan root).mapError .c4
  let reversed ← compiled.plan.precedence.reverse.foldlM (fun current name => do
    let some module := model.modules.find? (fun item => item.name == name)
      | throw (.missingModule name)
    let ancestors ← (LeanPoo.C4.linearize model.graph name).mapError .c4
    module.edits.foldlM (fun state edit => do
      let origins ← applyEdit name ancestors state.1 edit
      return (origins, { moduleName := name, edit } :: state.2))
      current) (([], []) : List PolicyOrigin × List AppliedEdit)
  let policies ← reversed.1.mapM fun origin => do
    let some (some policy) := compiled.resolve origin.id (fun _ => none)
      | throw (.inconsistentResolution origin.id)
    let compiled : CompiledPolicy :=
      { policy := policy, introducedBy := origin.introducedBy,
        lastEditedBy := origin.lastEditedBy }
    return compiled
  return (compiled, { policies, applied := reversed.2.reverse })

/-- C4 and compiled object slots choose policy bodies. The Cedar-specific fold
    checks edit intent, keeps policy order, and records provenance only. -/
def Model.compileWithTrace (model : Model) (root : String) :
    Except Error Compilation := do
  return (← model.compileWithPlan root).2

def Model.compileWithProvenance (model : Model) (root : String) :
    Except Error (List CompiledPolicy) :=
  (model.compileWithTrace root).map Compilation.policies

/-- Materialize the compiled policies for Cedar's validator and authorizer. -/
def Model.compile (model : Model) (root : String) : Except Error Policies :=
  (model.compileWithProvenance root).map (·.map CompiledPolicy.policy)

/-- Explain one policy ID after Cedar edit validation. Declaration nodes include
    tombstones; `effective` reports whether a policy survives those edits. -/
def Model.explainPolicy (model : Model) (root : String) (id : PolicyID) :
    Except Error PolicyExplanation := do
  let (compiled, compilation) ← model.compileWithPlan root
  let resolution := LeanPoo.Object.Debug.Plan.explain compiled.plan id
  return {
    resolution
    effective := compilation.policies.find? (fun item => item.policy.id == id)
    applied := compilation.applied.filter (fun item => item.edit.policyId == id) }

/-- Check a generated edit sequence with the same C4 compiler used by public
    policy modules. New policies append; existing policy order is preserved. -/
def Edit.replay (before : Policies) (edits : List Edit) : Except Error Policies :=
  ({ modules := [
      { name := "Before", edits := Edit.extendAll before },
      { name := "Next", parentOrders := [["Before"]], edits }] } : Model).compile "Next"

/-- A generated revision carries an equality receipt from the C4 compiler. -/
structure Reconciliation (before after : Policies) where
  edits : List Edit
  replays : Edit.replay before edits = .ok after

private def Edit.candidates (before after : Policies) : List Edit :=
  let removals := before.filterMap fun old =>
    if after.any (fun policy => policy.id == old.id) then none
    else some (.remove old.id)
  let overlays := after.filterMap fun policy =>
    match before.find? (fun old => old.id == policy.id) with
    | some old => if decide (old = policy) then none else some (.overlay policy)
    | none => none
  let extensions := after.filterMap fun policy =>
    if before.any (fun old => old.id == policy.id) then none
    else some (.extend policy)
  removals ++ overlays ++ extensions

/-- Turn a generated policy revision into extend, overlay, and remove edits.
    Reject duplicate IDs and ordering changes that these edits cannot express;
    the returned proof certifies the exact Cedar policy list after C4 replay. -/
def Edit.reconcile (before after : Policies) :
    Except Error (Reconciliation before after) :=
  if !(decide (before.map Policy.id).Nodup) then .error (.duplicateInputIds "before")
  else if !(decide (after.map Policy.id).Nodup) then .error (.duplicateInputIds "after")
  else
    let edits := Edit.candidates before after
    match replayed : Edit.replay before edits with
    | .error error => .error error
    | .ok actual =>
        if same : actual = after then
          .ok ⟨edits, by simpa [same] using replayed⟩
        else .error .unrepresentableOrder

/-- Compare policy bodies by ID, ignoring provenance-only changes. -/
def Compilation.changedPolicyIds (before after : Compilation) : List PolicyID :=
  let ids := ((before.policies.map (·.policy.id)) ++
    (after.policies.map (·.policy.id))).eraseDups
  ids.filter fun id =>
    let old : Option Policy :=
      (before.policies.find? (fun item => item.policy.id == id)).map (·.policy)
    let new : Option Policy :=
      (after.policies.find? (fun item => item.policy.id == id)).map (·.policy)
    !decide (old = new)

structure Revision where
  before : Compilation
  after : Compilation

def Model.compileRevision (model : Model) (beforeRoot afterRoot : String) :
    Except Error Revision := do
  return {
    before := (← model.compileWithTrace beforeRoot)
    after := (← model.compileWithTrace afterRoot)
  }

def Revision.changedPolicyIds (revision : Revision) : List PolicyID :=
  Compilation.changedPolicyIds revision.before revision.after

end CedarPooSpec.PolicyModules
