import CedarPooSpec.Gateway.Context
import CedarPooSpec.Admission.BoundOperation
import CedarPooSpec.Admission.PolicySnapshot
import Cedar.Validation.Validator
import Cedar.Validation.RequestEntityValidator

namespace CedarPooSpec.Gateway
open Cedar.Spec CedarPooSpec.PolicyModules
variable {Effect State : Type} {project : Effect → State → Request}

structure Prepared (Effect State : Type) (project : Effect → State → Request) where
  operationId : CedarPooSpec.Admission.OperationId
  operation : CedarPooSpec.Admission.BoundOperation Effect State project
  policy : CedarPooSpec.Admission.PolicySnapshot
  schema : Cedar.Validation.Schema
  context : Context
  profile : Profile
  sourceModules : List PolicyModules.Module

inductive Error where
  | invalidScope
  | invalidProfile
  | invalidPreparation
  | staleContext
  | staleSource
  | unqualifiedEvidence
  | invalidSchema
  | invalidRequest
  | invalidEntities
  | snapshot (error : CedarPooSpec.Admission.PolicySnapshot.Error)
  | operation (error : CedarPooSpec.Admission.Error)
  | denied
  deriving Repr

/-- A composable validation step retaining its proof for the final Receipt. -/
private def checkPremise (condition : Prop) [Decidable condition] (error : Error) :
    Except Error (PLift condition) :=
  if evidence : condition then .ok ⟨evidence⟩ else .error error

private def checkValidation (result : Except Failure Unit) (error : Error) :
    Except Error (PLift (result = .ok ())) :=
  match result with
  | .ok () => .ok ⟨rfl⟩
  | .error _ => .error error

/-- Preparation is transparent data. Recheck these conditions at authorization
so a direct structure constructor cannot bypass the public preparation path. -/
def Prepared.valid (prepared : Prepared Effect State project) : Bool :=
  prepared.context.scope.valid && prepared.profile.valid &&
  decide (prepared.profile.identity = prepared.context.scope.profile) &&
  decide (prepared.operationId.value = prepared.context.scope.canonicalOperation) &&
  !prepared.operationId.value.isEmpty && !prepared.policy.root.isEmpty &&
  prepared.schema.validateWellFormed.isOk &&
  (Cedar.Validation.validate prepared.policy.policies prepared.schema).isOk

/-- Pure preparation, not Host authentication, durable reservation or execution. -/
def prepare (model : Model) (root : String) (schema : Cedar.Validation.Schema)
    (context : Context) (profile : Profile)
    (project : Effect → State → Request) (effect : Effect) (state : State) :
    Except Error (Prepared Effect State project) := do
  let _ ← checkPremise (context.scope.valid = true) .invalidScope
  let _ ← checkPremise (root.isEmpty = false) .invalidScope
  let _ ← checkPremise (profile.valid = true ∧ profile.identity = context.scope.profile) .invalidProfile
  let snapshot ← (CedarPooSpec.Admission.PolicySnapshot.capture model root).mapError
    (fun error => .snapshot (.compilation error))
  let _ ← checkPremise (schema.validateWellFormed.isOk = true ∧
    (Cedar.Validation.validate snapshot.policies schema).isOk = true) .invalidSchema
  return ⟨⟨context.scope.canonicalOperation⟩, ⟨effect, state⟩, snapshot, schema, context, profile, model.modules⟩

/-- A proof-bearing semantic admission result. It is not a send handle. The Host
must still consume the original operation/authority and serialize actual use. -/
structure Receipt (prepared : Prepared Effect State project) (model : Model)
    (effect : Effect) (state : State) (actualContext : Context) (checks : List Assessment)
    (entities : Entities) where
  preparationValid : prepared.valid = true
  contextMatches : prepared.context = actualContext
  sourceMatches : prepared.sourceModules = model.modules
  effectMatches : prepared.operation.effect = effect
  stateMatches : prepared.operation.state = state
  checksAccepted : prepared.profile.accepts checks = true
  policyCurrent : ∃ policies, prepared.policy.currentPolicies model = .ok policies
  requestValid : Cedar.Validation.validateRequest prepared.schema (project effect state) = .ok ()
  entitiesValid : Cedar.Validation.validateEntities prepared.schema entities = .ok ()
  cedar : CedarPooSpec.CompoundAuthorization.Receipt model prepared.policy.root
    [prepared.operation.request] entities
  allowed : cedar.allowed = true

private def checkSnapshot (prepared : Prepared Effect State project) (model : Model) :
    Except Error (PLift (∃ policies, prepared.policy.currentPolicies model = .ok policies)) :=
  match prepared.policy.currentPolicies model with
  | .error error => .error (.snapshot error)
  | .ok policies => .ok ⟨⟨policies, rfl⟩⟩

def authorize [DecidableEq Effect] [DecidableEq State]
    (prepared : Prepared Effect State project) (model : Model)
    (effect : Effect) (state : State) (actualContext : Context)
    (checks : List Assessment) (entities : Entities) :
    Except Error (Receipt prepared model effect state actualContext checks entities) := do
  let valid ← checkPremise (prepared.valid = true) .invalidPreparation
  let context ← checkPremise (prepared.context = actualContext) .staleContext
  let source ← checkPremise (prepared.sourceModules = model.modules) .staleSource
  let actualEffect ← checkPremise (prepared.operation.effect = effect) (.operation .effectMismatch)
  let actualState ← checkPremise (prepared.operation.state = state) (.operation .stateMismatch)
  let evidence ← checkPremise (prepared.profile.accepts checks = true) .unqualifiedEvidence
  let current ← checkSnapshot prepared model
  let request ← checkValidation
    (Cedar.Validation.validateRequest prepared.schema (project effect state)) .invalidRequest
  let entityStore ← checkValidation
    (Cedar.Validation.validateEntities prepared.schema entities) .invalidEntities
  let cedar ← (prepared.operation.authorize effect state model prepared.policy.root entities).mapError Error.operation
  let allowed ← checkPremise (cedar.allowed = true) .denied
  return {
    preparationValid := valid.down
    contextMatches := context.down
    sourceMatches := source.down
    effectMatches := actualEffect.down
    stateMatches := actualState.down
    checksAccepted := evidence.down
    policyCurrent := current.down
    requestValid := request.down
    entitiesValid := entityStore.down
    cedar
    allowed := allowed.down }

theorem admitted_actual_request_is_error_free
    {E S : Type} {projection : E → S → Request} {prepared : Prepared E S projection}
    {model : Model} {actualEffect : E} {actualState : S} {actualContext : Context}
    {checks : List Assessment} {entities : Entities}
    (receipt : Receipt prepared model actualEffect actualState actualContext checks entities) :
    let response := isAuthorized (projection actualEffect actualState) entities receipt.cedar.policies
    (response.decision == .allow && response.erroringPolicies.isEmpty) = true := by
  have h := receipt.allowed
  simp only [CedarPooSpec.CompoundAuthorization.Receipt.allowed,
    receipt.cedar.evaluated, List.isEmpty_cons, Bool.not_false, Bool.true_and,
    List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true] at h
  simpa [CedarPooSpec.Admission.BoundOperation.request, receipt.effectMatches,
    receipt.stateMatches] using h

theorem admitted_context_is_current
    (receipt : Receipt prepared model effect state actualContext checks entities) :
    prepared.context = actualContext := receipt.contextMatches

theorem admitted_profile_preserves_required_checks
    (receipt : Receipt prepared model effect state actualContext checks entities) :
    ∀ check ∈ checks, check.status = .satisfied :=
  accepted_assessments_are_satisfied prepared.profile checks receipt.checksAccepted

end CedarPooSpec.Gateway
