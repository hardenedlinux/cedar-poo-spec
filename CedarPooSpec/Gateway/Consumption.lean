import CedarPooSpec.Gateway.ProfileAdmission
import CedarPooSpec.Admission.AuthorityConsumption

/-! Compose existing pure admission ledgers. The Host must authenticate their
source and commit both results with the reservation before any external effect. -/
namespace CedarPooSpec.Gateway

structure Consumed (Effect : Type) where
  operations : CedarPooSpec.Admission.OperationLedger
  authorities : CedarPooSpec.Admission.AuthorityLedger Effect

inductive ConsumptionError where
  | operationAlreadyAdmitted
  | authority (error : CedarPooSpec.Admission.AuthorityLedger.Error)
  deriving BEq, Repr

/-- The original operation ID, not a renewed grant ID, owns deduplication.
Errors return no partial updated state. This function performs no IO or send. -/
def consumeAdmission {E S : Type} {project : E → S → Cedar.Spec.Request}
    {prepared : Prepared E S project} {model : CedarPooSpec.PolicyModules.Model}
    {effect : E} {state : S} {actualContext : Context} {checks : List Assessment}
    {entities : Cedar.Spec.Entities} [BEq E] [LawfulBEq E]
    {original : Profile} {object : ProfileObject.Object}
    (publication : ProfileObject.Publication original object)
    (_receipt : PublishedReceipt publication prepared model effect state actualContext checks entities)
    (operations : CedarPooSpec.Admission.OperationLedger)
    (authorities : CedarPooSpec.Admission.AuthorityLedger E) (authorityId : String) :
    Except ConsumptionError (Consumed E) := do
  let updatedOperations ← (operations.admit prepared.operationId).elim
    (.error ConsumptionError.operationAlreadyAdmitted) Except.ok
  let updatedAuthorities ← (authorities.consume authorityId effect).mapError ConsumptionError.authority
  return ⟨updatedOperations, updatedAuthorities⟩

section Laws
variable {E S : Type} {project : E → S → Cedar.Spec.Request}
  {prepared : Prepared E S project} {model : CedarPooSpec.PolicyModules.Model}
  {effect : E} {state : S} {actualContext : Context} {checks : List Assessment}
  {entities : Cedar.Spec.Entities} [BEq E] [LawfulBEq E]
  {original : Profile} {object : ProfileObject.Object}
  (publication : ProfileObject.Publication original object)
  (receipt : PublishedReceipt publication prepared model effect state actualContext checks entities)
  (operations : CedarPooSpec.Admission.OperationLedger)
  (authorities : CedarPooSpec.Admission.AuthorityLedger E) (authorityId : String)

/-- Successful composition preserves the entire existing operation prefix and
adds exactly the original operation, irrespective of the authority identifier. -/
theorem consumption_preserves_operation_prefix (result : Consumed E)
    (committed : consumeAdmission publication receipt operations authorities authorityId = .ok result) :
    result.operations.admitted = operations.admitted ++ [prepared.operationId] := by
  cases op : operations.admit prepared.operationId <;>
    cases grant : authorities.consume authorityId effect <;>
    simp_all [consumeAdmission, CedarPooSpec.Admission.OperationLedger.admit,
      Except.mapError]
  grind only

/-- Replay rejection is conditional on using the returned ledger. Persisting,
serializing and recovering that ledger is a Host obligation. -/
theorem consumed_operation_rejects_replay (result : Consumed E)
    (committed : consumeAdmission publication receipt operations authorities authorityId = .ok result) :
    result.operations.admit prepared.operationId = none := by
  have historyPrefix := consumption_preserves_operation_prefix publication receipt operations authorities authorityId result committed
  have reflexive : (prepared.operationId == prepared.operationId) = true := by
    change (prepared.operationId.value == prepared.operationId.value) = true
    simp
  simp [CedarPooSpec.Admission.OperationLedger.admit,
    CedarPooSpec.Admission.OperationLedger.check, historyPrefix, List.contains_append,
    reflexive]

theorem renewed_authority_cannot_repeat_consumed_operation (result : Consumed E)
    (committed : consumeAdmission publication receipt operations authorities authorityId = .ok result)
    (renewedAuthorities : CedarPooSpec.Admission.AuthorityLedger E) (renewedId : String) :
    consumeAdmission publication receipt result.operations renewedAuthorities renewedId =
      .error .operationAlreadyAdmitted := by
  simp [consumeAdmission,
    consumed_operation_rejects_replay publication receipt operations authorities authorityId result committed]

end Laws

end CedarPooSpec.Gateway
