import CedarPooSpec.Authorization.Delta.Model
import LeanPoo.Proof.Invalidation

/-!
Explain a symbolic authorization delta using the same C4 compilation and
proof-dependency structures that produced its policy revision. Edit provenance
identifies candidate changes; it does not claim that one edit alone caused a
symbolic witness when multiple policy bodies changed.
-/

namespace CedarPooSpec.Authorization.Delta

open Cedar.Spec CedarPooSpec.PolicyModules LeanPoo.Proof

/-- One policy body's owner metadata in a compiled C4 root. -/
structure PolicyOwner where
  introducedBy : String
  lastEditedBy : String
  deriving DecidableEq, Repr

/-- The three native POO policy edit forms. -/
inductive EditKind where
  | extend | overlay | remove
  deriving DecidableEq, Repr

/-- One applied POO operation affecting a policy ID. -/
structure EditSource where
  moduleName : String
  operation : EditKind
  deriving DecidableEq, Repr

/-- The before and after provenance of one changed policy body. -/
structure PolicyChange where
  id : PolicyID
  beforeOwner : Option PolicyOwner
  afterOwner : Option PolicyOwner
  beforeEdits : List EditSource
  afterEdits : List EditSource
  deriving Repr

private def owner? (compilation : Compilation) (id : PolicyID) : Option PolicyOwner :=
  (compilation.policies.find? (fun entry => entry.policy.id == id)).map fun entry =>
    ⟨entry.introducedBy, entry.lastEditedBy⟩

private def editSource (applied : AppliedEdit) : EditSource :=
  { moduleName := applied.moduleName
    operation := match applied.edit with
      | .extend _ => .extend
      | .overlay _ => .overlay
      | .remove _ => .remove }

private def editsFor (compilation : Compilation) (id : PolicyID) : List EditSource :=
  (compilation.applied.filter (fun entry => entry.edit.policyId == id)).map editSource

/-- Policy-body changes with both compiled owners and edit trails. -/
def Revision.policyChanges (revision : Revision) : List PolicyChange :=
  revision.changedPolicyIds.map fun id =>
    { id
      beforeOwner := owner? revision.before id
      afterOwner := owner? revision.after id
      beforeEdits := editsFor revision.before id
      afterEdits := editsFor revision.after id }

/-- Changes to the compiled POO owner or edit history, including an overlay
    that leaves the Cedar policy body and ID unchanged. This is a governance
    provenance delta, not an authorization behavior delta. -/
def Revision.provenanceChanges (revision : Revision) : List PolicyChange :=
  let ids := ((revision.before.policies.map (·.policy.id)) ++
    (revision.after.policies.map (·.policy.id))).eraseDups
  ids.filterMap fun id =>
    let beforeOwner := owner? revision.before id
    let afterOwner := owner? revision.after id
    let beforeEdits := editsFor revision.before id
    let afterEdits := editsFor revision.after id
    if beforeOwner == afterOwner && beforeEdits == afterEdits then none
    else some { id, beforeOwner, afterOwner, beforeEdits, afterEdits }

/-- Exact policy bodies needing new per-policy validation, plus the unchanged
    bodies whose certified validation can be reused with the same schema. -/
structure ProofFootprint where
  freshPolicyIds : List PolicyID
  reusedPolicyIds : List PolicyID
  authorizationDependencies : List CedarPooSpec.Soundness.AuthorizationKey

/-- Derive validation reuse and authorization invalidation from the existing
    proof-object patches rather than a second dependency model. -/
def Revision.proofFootprint (revision : Revision) : ProofFootprint :=
  { freshPolicyIds := revision.freshPolicies.map Policy.id
    reusedPolicyIds := (revision.afterPolicies.filter fun policy =>
      decide (policy ∈ revision.beforePolicies)).map Policy.id
    authorizationDependencies := changedDependencies
      CedarPooSpec.Soundness.policiesObligation revision.authorizationPatch }

/-- Last editors on both sides of every changed policy, without duplicates. -/
def invalidationOwners (changes : List PolicyChange) : List String :=
  let beforeOwners := changes.filterMap fun change =>
    change.beforeEdits.getLast?.map (·.moduleName)
  let afterOwners := changes.filterMap fun change =>
    change.afterEdits.getLast?.map (·.moduleName)
  (beforeOwners ++ afterOwners).eraseDups

/-- C4 descendants whose compilation may depend on the last editor on either
    side of a changed policy. The roots may be siblings, so both branches
    contribute. This is an invalidation set, not a behavioral witness or proof
    of individual edit causality. -/
def affectedRoots (model : Model) (changes : List PolicyChange) : List String :=
  invalidatedNodes model.graph (invalidationOwners changes)

theorem affectedRoots_iff_bounded_descendant (model : Model)
    (changes : List PolicyChange) (name : String) :
    name ∈ affectedRoots model changes ↔
      ∃ origin ∈ invalidationOwners changes, ∃ steps,
        steps ≤ model.graph.nodes.length ∧
          Descendant model.graph origin steps name := by
  exact mem_invalidated_iff_bounded_descendant model.graph
    (invalidationOwners changes) name

theorem beforeEditorIsInvalidationOwner (changes : List PolicyChange)
    (change : PolicyChange) (source : EditSource)
    (member : change ∈ changes)
    (last : change.beforeEdits.getLast? = some source) :
    source.moduleName ∈ invalidationOwners changes := by
  simp only [invalidationOwners, List.mem_eraseDups, List.mem_append]
  left
  apply List.mem_filterMap.mpr
  exact ⟨change, member, by simp [last]⟩

theorem afterEditorIsInvalidationOwner (changes : List PolicyChange)
    (change : PolicyChange) (source : EditSource)
    (member : change ∈ changes)
    (last : change.afterEdits.getLast? = some source) :
    source.moduleName ∈ invalidationOwners changes := by
  simp only [invalidationOwners, List.mem_eraseDups, List.mem_append]
  right
  apply List.mem_filterMap.mpr
  exact ⟨change, member, by simp [last]⟩

theorem beforeEditorDescendantInvalidated (model : Model)
    (changes : List PolicyChange) (change : PolicyChange) (source : EditSource)
    (name : String) (steps : Nat)
    (member : change ∈ changes)
    (last : change.beforeEdits.getLast? = some source)
    (path : Descendant model.graph source.moduleName steps name)
    (withinBound : steps ≤ model.graph.nodes.length) :
    name ∈ affectedRoots model changes := by
  exact mem_invalidated_of_descendant model.graph (invalidationOwners changes)
    source.moduleName name steps
    (beforeEditorIsInvalidationOwner changes change source member last)
    path withinBound

theorem afterEditorDescendantInvalidated (model : Model)
    (changes : List PolicyChange) (change : PolicyChange) (source : EditSource)
    (name : String) (steps : Nat)
    (member : change ∈ changes)
    (last : change.afterEdits.getLast? = some source)
    (path : Descendant model.graph source.moduleName steps name)
    (withinBound : steps ≤ model.graph.nodes.length) :
    name ∈ affectedRoots model changes := by
  exact mem_invalidated_of_descendant model.graph (invalidationOwners changes)
    source.moduleName name steps
    (afterEditorIsInvalidationOwner changes change source member last)
    path withinBound

/-- Symbolic result together with C4 provenance and proof-reuse footprint. -/
structure ExplainedReport where
  beforeRoot : String
  afterRoot : String
  symbolic : Report
  changes : List PolicyChange
  proof : ProofFootprint
  potentiallyInvalidatedRoots : List String

/-- Both authorization directions with the same C4 and proof evidence. -/
structure ExplainedImpactReport where
  beforeRoot : String
  afterRoot : String
  symbolic : ImpactReport
  changes : List PolicyChange
  proof : ProofFootprint
  potentiallyInvalidatedRoots : List String

/-- Compile one POO revision once, run Cedar's symbolic implication query,
    and attach the exact owner and dependency metadata of that revision. -/
def analyzeModelExplained (model : Model) (beforeRoot afterRoot : String)
    (schema : Cedar.Validation.Schema) : IO (Except Error ExplainedReport) := do
  let revision ← match model.compileRevision beforeRoot afterRoot with
    | .ok revision => pure revision
    | .error error => return .error (.compilation error)
  let result ← analyze revision schema
  return result.map fun symbolic =>
    let changes := Revision.policyChanges revision
    { beforeRoot, afterRoot, symbolic, changes
      proof := Revision.proofFootprint revision
      potentiallyInvalidatedRoots := affectedRoots model changes }

/-- Query gains and losses, retaining the revision's owner, patch, and proof
    footprint. An empty pair of witness lists means no change in the covered
    Cedar schema environments, subject to the solver boundary. -/
def analyzeModelImpactExplained (model : Model) (beforeRoot afterRoot : String)
    (schema : Cedar.Validation.Schema) : IO (Except Error ExplainedImpactReport) := do
  let revision ← match model.compileRevision beforeRoot afterRoot with
    | .ok revision => pure revision
    | .error error => return .error (.compilation error)
  let result ← analyzeImpact revision schema
  return result.map fun symbolic =>
    let changes := Revision.policyChanges revision
    { beforeRoot, afterRoot, symbolic, changes
      proof := Revision.proofFootprint revision
      potentiallyInvalidatedRoots := affectedRoots model changes }

end CedarPooSpec.Authorization.Delta
