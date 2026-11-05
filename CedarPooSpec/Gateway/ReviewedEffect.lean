import CedarPooSpec.Gateway.EffectProtocol
import CedarPooSpec.Gateway.PublicationReview

namespace CedarPooSpec.Gateway.ReviewedEffect
open LeanPoo.Functional.DeclarativeMetadata
open Authorization.Delta Cedar.Spec

/-- The actual POO Contract binds the whole successor, not only an approval bit. -/
def contract (reviewed : ReviewedInteraction) (model : PolicyModules.Model)
    (schema : Cedar.Validation.Schema) (before : ReleaseState) :
    Contract Unit Bool (ReleaseState × Policies) where
  input := ⟨"reviewed-publication", fun _ => True, fun _ => inferInstance⟩
  output := ⟨"installed-release", fun _ => True, fun _ => inferInstance⟩
  meaning := fun _ approved result =>
    (reviewed.advanceReviewed model schema before (fun _ _ => approved)).toOption = some result
  decide := fun _ _ _ => inferInstance
  rule := .atom ()

def prepare (reviewed : ReviewedInteraction) (model : PolicyModules.Model)
    (schema : Cedar.Validation.Schema) (before : ReleaseState) (_ : Unit) (approved : Bool) :=
  (reviewed.advanceReviewed model schema before (fun _ _ => approved)).map (fun next => (next, ()))

def invoke (reviewed : ReviewedInteraction) (model : PolicyModules.Model)
    (schema : Cedar.Validation.Schema) (before : ReleaseState) (approved : Bool) :=
  (contract reviewed model schema before).invoke (prepare reviewed model schema before ()) approved

theorem invocation_installs_exact_successor
    (receipt : Invocation (contract reviewed model schema before)
      (prepare reviewed model schema before ()) approved) :
    reviewed.advanceReviewed model schema before (fun _ _ => approved) = .ok receipt.result := by
  have bound := receipt.logic
  simp only [contract, Formula.Holds] at bound
  cases result : reviewed.advanceReviewed model schema before (fun _ _ => approved) with
  | error error =>
      rw [result] at bound
      change none = some receipt.result at bound
      contradiction
  | ok value =>
      rw [result] at bound
      change some value = some receipt.result at bound
      exact congrArg Except.ok (Option.some.inj bound)

/-- Join the actual reviewed transition to the actual current Cedar receipt. -/
theorem invocation_then_current_effect
    (publication : Invocation (contract reviewed model schema before)
      (prepare reviewed model schema before ()) approved)
    {E S : Type} {project : E → S → Request}
    {prepared : Gateway.Prepared E S project} {activeModel : PolicyModules.Model}
    {effect : E} {state : S} {context : Gateway.Context}
    {checks : List Gateway.Assessment} {entities : Entities}
    (receipt : Gateway.Receipt prepared activeModel effect state context checks entities)
    (installed : publication.result.1.matchesCurrent
      ⟨prepared.policy.root, receipt.cedar.policies⟩ context.policyRevision = true)
    (current : EffectProtocol.Current) (envelope : EffectProtocol.Envelope)
    (accepted : EffectProtocol.accepts current envelope receipt.cedar.allowed = true) :
    reviewed.advanceReviewed model schema before (fun _ _ => approved) = .ok publication.result ∧
      publication.result.1.epoch = before.epoch + 1 ∧
      envelope.effect = current.effect ∧ envelope.review = current.review ∧
      errorFreeAllow publication.result.1.activePolicies
        (Env.mk (project effect state) entities) = true := by
  have committed := invocation_installs_exact_successor publication
  have post := reviewed.advanceReviewed_postcondition model schema before
    publication.result.1 publication.result.2 (fun _ _ => approved) committed
  have currentPolicies := (ReleaseState.matchesCurrent_iff _ _ _).mp installed
  have allowed := Gateway.admitted_actual_request_is_error_free receipt
  have binding := EffectProtocol.accepted_effect_is_exact current envelope receipt.cedar.allowed accepted
  change errorFreeAllow receipt.cedar.policies (Env.mk (project effect state) entities) = true at allowed
  have samePolicies : publication.result.1.activePolicies = receipt.cedar.policies := currentPolicies.2.1
  rw [← samePolicies] at allowed
  exact ⟨committed, by simpa using congrArg ReleaseState.epoch post.2,
    binding.1, binding.2.1, allowed⟩
section FinalJoin
variable {Command Result View Parent Artifact Cut Atom Error : Type}
  [DecidableEq Command] [DecidableEq Parent] [DecidableEq Artifact] [DecidableEq Cut]
/-- The existing Final keeps registration, fencing, original Contract and Zero
Trust premises when joined to a fresh use of the actual installed policies. -/
theorem actual_final_then_current_effect
    {host : PublicationReview.Host Command Result View Parent Artifact Cut}
    {resolve modelAt schemaAt stateAt frontierAt approveGain}
    {template : Contract Atom Command Result}
    {operation : View → Command → Except Error (Result × View)} {command actual}
    (publication : PublicationReview.Final
      (host.withDeltaReview resolve modelAt schemaAt stateAt frontierAt approveGain)
      template operation command actual)
    {E S : Type} {project : E → S → Request}
    {prepared : Gateway.Prepared E S project} {activeModel : PolicyModules.Model}
    {effect : E} {state : S} {context : Gateway.Context}
    {checks : List Gateway.Assessment} {entities : Entities}
    (receipt : Gateway.Receipt prepared activeModel effect state context checks entities)
    (installed : (stateAt publication.receipt.state).matchesCurrent
      ⟨prepared.policy.root, receipt.cedar.policies⟩ context.policyRevision = true) :
    template.rule.Holds (fun atom => template.meaning atom command publication.receipt.result) ∧
      host.security.required command actual ∧
      (∃ artifact reviewed policies,
        host.approvedEvidenceAt actual command = some artifact ∧
        resolve actual command artifact = some reviewed ∧
        reviewed.advanceReviewed (modelAt actual) (schemaAt actual) (stateAt actual)
          (approveGain actual command) = .ok (stateAt publication.receipt.state, policies)) ∧
      errorFreeAllow (stateAt publication.receipt.state).activePolicies
        (Env.mk (project effect state) entities) = true := by
  have reviewed := PublicationReview.delta_final_retains_exact_review publication
  have original := (PublicationReview.final_preserves_original_and_binding publication).1
  have same := (ReleaseState.matchesCurrent_iff _ _ _).mp installed
  have allowed := Gateway.admitted_actual_request_is_error_free receipt
  change errorFreeAllow receipt.cedar.policies (Env.mk (project effect state) entities) = true at allowed
  have policies : (stateAt publication.receipt.state).activePolicies = receipt.cedar.policies := same.2.1
  rw [← policies] at allowed
  exact ⟨original, publication.current, reviewed.2, allowed⟩
end FinalJoin

end CedarPooSpec.Gateway.ReviewedEffect
