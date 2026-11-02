import CedarPooSpec.Evaluation
import CedarPooSpec.Validation
import LeanPoo.Proof.Product

/-!
Compose the independent Cedar evaluation and typechecking certificates.
Keys remain disjoint, so an evaluation patch leaves typechecking obligations
outside its invalidation footprint and conversely.
-/

namespace CedarPooSpec.Composition

open LeanPoo.Proof

abbrev Key := Sum Evaluation.Key Validation.Key
abbrev Value := SumValue Evaluation.Value Validation.Value

def proofObject (evaluation : Evaluation.Snapshot)
    (validation : Validation.Snapshot) : ProofObject Key Value :=
  evaluation.proofObject.pair validation.proofObject

theorem certificate (evaluation : Evaluation.Snapshot)
    (validation : Validation.Snapshot)
    (evaluationValid : evaluation.result =
      Cedar.Spec.evaluate evaluation.expr evaluation.request evaluation.entities)
    (validationValid : validation.result =
      Cedar.Validation.typecheckPolicy validation.policy validation.environment) :
    Certificate (proofObject evaluation validation) :=
  Certificate.pair evaluation.proofObject validation.proofObject
    (evaluation.certificate evaluationValid)
    (validation.certificate validationValid)

def replaceExprPatch (evaluation : Evaluation.Snapshot)
    (expr : Cedar.Spec.Expr) : Patch Key Value :=
  (Evaluation.replaceExprPatch evaluation expr).left

def replacePolicyPatch (validation : Validation.Snapshot)
    (policy : Cedar.Spec.Policy) : Patch Key Value :=
  (Validation.replacePolicyPatch validation policy).right

/-- The evaluator input is the expression of the policy being checked. -/
def alignmentObligation : Obligation Key Value where
  dependencies := [.inl .expr, .inr .policy]
  holds := fun state =>
    state (.inl .expr) = (state (.inr .policy)).toExpr
  stable := by
    intro before after equal holds
    have he : before (.inl .expr) = after (.inl .expr) :=
      equal (.inl .expr) (by simp)
    have hp : before (.inr .policy) = after (.inr .policy) :=
      equal (.inr .policy) (by simp)
    simpa [he, hp] using holds

def alignedProofObject (evaluation : Evaluation.Snapshot)
    (validation : Validation.Snapshot) : ProofObject Key Value :=
  (proofObject evaluation validation).withObligation alignmentObligation

theorem alignedCertificate (evaluation : Evaluation.Snapshot)
    (validation : Validation.Snapshot)
    (evaluationValid : evaluation.result =
      Cedar.Spec.evaluate evaluation.expr evaluation.request evaluation.entities)
    (validationValid : validation.result =
      Cedar.Validation.typecheckPolicy validation.policy validation.environment)
    (aligned : evaluation.expr = validation.policy.toExpr) :
    Certificate (alignedProofObject evaluation validation) :=
  Certificate.withObligation (proofObject evaluation validation)
    (certificate evaluation validation evaluationValid validationValid)
    alignmentObligation aligned

theorem expression_change_affects_alignment
    (evaluation : Evaluation.Snapshot) (_validation : Validation.Snapshot)
    (expr : Cedar.Spec.Expr) :
    changedDependencies alignmentObligation
      (replaceExprPatch evaluation expr) = [.inl .expr] := by
  simp [changedDependencies, alignmentObligation, replaceExprPatch,
    Evaluation.replaceExprPatch, Patch.left, Patch.then, Patch.set]

theorem policy_change_affects_alignment
    (_evaluation : Evaluation.Snapshot) (validation : Validation.Snapshot)
    (policy : Cedar.Spec.Policy) :
    changedDependencies alignmentObligation
      (replacePolicyPatch validation policy) = [.inr .policy] := by
  simp [changedDependencies, alignmentObligation, replacePolicyPatch,
    Validation.replacePolicyPatch, Patch.right, Patch.then, Patch.set]

theorem typecheck_reused_after_expr_change
    (evaluation : Evaluation.Snapshot)
    (validation : Validation.Snapshot)
    (evaluationValid : evaluation.result =
      Cedar.Spec.evaluate evaluation.expr evaluation.request evaluation.entities)
    (validationValid : validation.result =
      Cedar.Validation.typecheckPolicy validation.policy validation.environment)
    (expr : Cedar.Spec.Expr) :
    Validation.typecheckObligation.right.holds
      (append (proofObject evaluation validation)
        (replaceExprPatch evaluation expr)).state := by
  apply reuse (proofObject evaluation validation)
    (replaceExprPatch evaluation expr)
    (certificate evaluation validation evaluationValid validationValid)
    Validation.typecheckObligation.right
  · simp [proofObject, ProofObject.pair, Validation.Snapshot.proofObject]
  · exact Obligation.right_unaffected_left
      Validation.typecheckObligation (Evaluation.replaceExprPatch evaluation expr)

theorem evaluation_reused_after_policy_change
    (evaluation : Evaluation.Snapshot)
    (validation : Validation.Snapshot)
    (evaluationValid : evaluation.result =
      Cedar.Spec.evaluate evaluation.expr evaluation.request evaluation.entities)
    (validationValid : validation.result =
      Cedar.Validation.typecheckPolicy validation.policy validation.environment)
    (policy : Cedar.Spec.Policy) :
    Evaluation.evaluationObligation.left.holds
      (append (proofObject evaluation validation)
        (replacePolicyPatch validation policy)).state := by
  apply reuse (proofObject evaluation validation)
    (replacePolicyPatch validation policy)
    (certificate evaluation validation evaluationValid validationValid)
    Evaluation.evaluationObligation.left
  · simp [proofObject, ProofObject.pair, Evaluation.Snapshot.proofObject]
  · exact Obligation.left_unaffected_right
      Evaluation.evaluationObligation (Validation.replacePolicyPatch validation policy)

end CedarPooSpec.Composition
