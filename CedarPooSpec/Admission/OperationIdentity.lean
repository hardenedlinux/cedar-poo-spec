import Lean.Data.Json

/-!
One authenticated workflow operation remains the same operation across
approval renewal, Agent replanning, and retries. This pure ledger records
admission, not delivery; the Host must persist it transactionally.
-/

namespace CedarPooSpec.Admission

structure OperationId where
  value : String
  deriving BEq, Repr

structure OperationLedger where
  admitted : List OperationId := []
  deriving BEq, Repr

namespace OperationLedger

def check (ledger : OperationLedger) (id : OperationId) : Bool :=
  !id.value.isEmpty && !ledger.admitted.contains id

def admit (ledger : OperationLedger) (id : OperationId) : Option OperationLedger :=
  if ledger.check id then some { admitted := ledger.admitted ++ [id] } else none

end OperationLedger
end CedarPooSpec.Admission
