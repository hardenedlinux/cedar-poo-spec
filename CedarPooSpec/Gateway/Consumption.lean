import CedarPooSpec.Gateway.Admission
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
    {entities : Cedar.Spec.Entities} [BEq E]
    (_receipt : Receipt prepared model effect state actualContext checks entities)
    (operations : CedarPooSpec.Admission.OperationLedger)
    (authorities : CedarPooSpec.Admission.AuthorityLedger E) (authorityId : String) :
    Except ConsumptionError (Consumed E) := do
  let updatedOperations ← (operations.admit prepared.operationId).elim
    (.error ConsumptionError.operationAlreadyAdmitted) Except.ok
  let updatedAuthorities ← (authorities.consume authorityId effect).mapError ConsumptionError.authority
  return ⟨updatedOperations, updatedAuthorities⟩

end CedarPooSpec.Gateway
