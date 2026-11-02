import CedarPooSpec.Functional.CompilationJson
import CedarPooSpec.Authorization.Delta.Evidence
import CedarPooSpec.PolicyJson

/-! JSON projection for authorization-delta reports and Cedar replay cases. -/

namespace CedarPooSpec.Authorization.Delta.Json

open CedarPooSpec.Authorization.Delta CedarPooSpec.PolicyModules

private def change (witness : Cedar.Spec.Env)
    (beforeResponse afterResponse : Cedar.Spec.Response) : Except String Lean.Json := do
  let request ← CedarPooSpec.PolicyJson.request witness.request |>.mapError reprStr
  let entities ← CedarPooSpec.PolicyJson.entities witness.entities |>.mapError reprStr
  return Lean.Json.mkObj [
    ("request", request),
    ("entities", entities),
    ("before_decision", Lean.toJson beforeResponse.decision),
    ("after_decision", Lean.toJson afterResponse.decision),
    ("before_reasons", Lean.toJson beforeResponse.determiningPolicies.toList),
    ("after_reasons", Lean.toJson afterResponse.determiningPolicies.toList)]

def expansion (item : Expansion) : Except String Lean.Json :=
  change item.witness item.beforeResponse item.afterResponse

def contraction (item : Contraction) : Except String Lean.Json :=
  change item.witness item.beforeResponse item.afterResponse

def report (item : Report) : Except String Lean.Json := do
  let expansions ← item.expansions.mapM expansion
  return Lean.Json.mkObj [
    ("status", Lean.toJson (if item.noExpansion then "no-expansion-in-schema" else "expanded")),
    ("changed_policy_ids", Lean.toJson item.changedPolicyIds),
    ("environments_checked", Lean.toJson item.environmentsChecked),
    ("counterexamples", Lean.toJson expansions)]

private def ownerJson : Option PolicyOwner → Lean.Json
  | none => .null
  | some owner => Lean.Json.mkObj [
      ("introduced_by", Lean.toJson owner.introducedBy),
      ("last_edited_by", Lean.toJson owner.lastEditedBy)]

private def editKindName : EditKind → String
  | .extend => "extend"
  | .overlay => "overlay"
  | .remove => "remove"

private def editJson (source : EditSource) : Lean.Json :=
  Lean.Json.mkObj [
    ("module", Lean.toJson source.moduleName),
    ("operation", Lean.toJson (editKindName source.operation))]

private def changeJson (change : PolicyChange) : Lean.Json :=
  Lean.Json.mkObj [
    ("policy_id", Lean.toJson change.id),
    ("before_owner", ownerJson change.beforeOwner),
    ("after_owner", ownerJson change.afterOwner),
    ("before_edits", Lean.toJson (change.beforeEdits.map editJson)),
    ("after_edits", Lean.toJson (change.afterEdits.map editJson))]

private def dependencyName : CedarPooSpec.Soundness.AuthorizationKey → String
  | .policies => "policies"
  | .schema => "schema"
  | .request => "request"
  | .entities => "entities"

/-- Source and proof-reuse evidence for a Cedar symbolic result. The policy
    edits are candidate origins, not a counterfactual attribution theorem. -/
private def explanation (beforeRoot afterRoot : String) (changes : List PolicyChange)
    (proof : ProofFootprint) (invalidatedRoots : List String) : Lean.Json :=
  Lean.Json.mkObj [
    ("before_root", Lean.toJson beforeRoot),
    ("after_root", Lean.toJson afterRoot),
    ("changes", Lean.toJson (changes.map changeJson)),
    ("proof", Lean.Json.mkObj [
      ("fresh_policy_ids", Lean.toJson proof.freshPolicyIds),
      ("reused_policy_ids", Lean.toJson proof.reusedPolicyIds),
      ("authorization_dependencies", Lean.toJson
        (proof.authorizationDependencies.map dependencyName))]),
    ("potentially_invalidated_roots", Lean.toJson invalidatedRoots)]

def explainedReport (item : ExplainedReport) : Lean.Json :=
  explanation item.beforeRoot item.afterRoot item.changes item.proof
    item.potentiallyInvalidatedRoots

def explainedImpactReport (item : ExplainedImpactReport) : Lean.Json :=
  explanation item.beforeRoot item.afterRoot item.changes item.proof
    item.potentiallyInvalidatedRoots

def impactReport (item : ImpactReport) : Except String Lean.Json := do
  let gains ← item.gains.mapM expansion
  let losses ← item.losses.mapM contraction
  return Lean.Json.mkObj [
    ("classification", Lean.toJson item.classification),
    ("changed_policy_ids", Lean.toJson item.changedPolicyIds),
    ("environments_checked", Lean.toJson item.environmentsChecked),
    ("gains", Lean.toJson gains),
    ("losses", Lean.toJson losses)]

def witnessCases (item : Report) (model : Model)
    (beforeRoot afterRoot : String) : Except String Lean.Json := do
  let compiler := CedarPooSpec.Functional.compilation model
  let cases ← item.expansions.zipIdx.mapM fun (entry, index) => do
    let before ← compiler.authorizationCase
        s!"delta-before-{index}" beforeRoot beforeRoot entry.witness.request entry.witness.entities
    let after ← compiler.authorizationCase
        s!"delta-after-{index}" afterRoot afterRoot entry.witness.request entry.witness.entities
    return [before, after]
  return Lean.Json.mkObj [("cases", Lean.toJson cases.flatten)]

/-- Replay both directions using the original before and after roots. -/
def impactWitnessCases (item : ImpactReport) (model : Model)
    (beforeRoot afterRoot : String) : Except String Lean.Json := do
  let compiler := CedarPooSpec.Functional.compilation model
  let witnesses := item.gains.map (·.witness) ++ item.losses.map (·.witness)
  let cases ← witnesses.zipIdx.mapM fun (witness, index) => do
    let before ← compiler.authorizationCase
        s!"impact-before-{index}" beforeRoot beforeRoot witness.request witness.entities
    let after ← compiler.authorizationCase
        s!"impact-after-{index}" afterRoot afterRoot witness.request witness.entities
    return [before, after]
  return Lean.Json.mkObj [("cases", Lean.toJson cases.flatten)]

/-- Preserve both concrete Host snapshots; they need not share context or
    entity attributes, only the principal/action/resource identity. -/
def snapshotReport (item : SnapshotImpact) (before after : Cedar.Spec.Env) :
    Except String Lean.Json := do
  let beforeRequest ← CedarPooSpec.PolicyJson.request before.request |>.mapError reprStr
  let afterRequest ← CedarPooSpec.PolicyJson.request after.request |>.mapError reprStr
  let beforeEntities ← CedarPooSpec.PolicyJson.entities before.entities |>.mapError reprStr
  let afterEntities ← CedarPooSpec.PolicyJson.entities after.entities |>.mapError reprStr
  return Lean.Json.mkObj [
    ("before_request", beforeRequest), ("after_request", afterRequest),
    ("before_entities", beforeEntities), ("after_entities", afterEntities),
    ("before_decision", Lean.toJson item.beforeResponse.decision),
    ("after_decision", Lean.toJson item.afterResponse.decision)]

def snapshotCases (name : String) (model : Model) (beforeRoot afterRoot : String)
    (before after : Cedar.Spec.Env) : Except String Lean.Json := do
  let compiler := CedarPooSpec.Functional.compilation model
  let beforeCase ← compiler.authorizationCase
      s!"{name}-before" beforeRoot beforeRoot before.request before.entities
  let afterCase ← compiler.authorizationCase
      s!"{name}-after" afterRoot afterRoot after.request after.entities
  return Lean.Json.mkObj [("cases", Lean.toJson [beforeCase, afterCase])]

end CedarPooSpec.Authorization.Delta.Json
