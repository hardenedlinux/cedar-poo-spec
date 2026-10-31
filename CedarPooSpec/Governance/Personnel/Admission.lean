import CedarPooSpec.Governance.Personnel.AssetAccess
import CedarPooSpec.Governance.Personnel.KnowledgeScope

/-!
Compose a POO/Cedar operation receipt with a cumulative personnel knowledge
boundary. The Host still authenticates every input and atomically commits the
real effect and observation ledger; this pure function cannot do either.
-/

namespace CedarPooSpec.Governance.Personnel

open Cedar.Spec CedarPooSpec.PolicyModules

inductive AdmissionError where
  | operation (error : CedarPooSpec.Admission.Error)
  | policyDenied
  | knowledge (error : KnowledgeScope.AdmissionError)
  deriving Repr

/-- Admit one actual operation and its resulting observation against the same
    compiled POO root. The caller chooses an owner-curated boundary suitable
    for this person and task. -/
def authorizeAndObserve {Fact : Type} [BEq Fact]
    (model : Model) (root : String) (entities : Entities)
    (operation : AssetAccess.Operation)
    (actualEffect : AssetAccess.Effect) (actualState : AssetAccess.Snapshot)
    (catalog : List (KnowledgeScope.Fragment EntityUID Fact))
    (boundary : KnowledgeScope.Boundary Fact)
    (ledger : KnowledgeScope.Ledger EntityUID) :
    Except AdmissionError
      ((CedarPooSpec.Authorization.Compound.Receipt model root
        [operation.request] entities) × KnowledgeScope.Ledger EntityUID) := do
  let receipt ← (CedarPooSpec.Admission.BoundOperation.authorize operation
    actualEffect actualState model root entities).mapError .operation
  if !receipt.allowed then
    throw .policyDenied
  let updated ← (KnowledgeScope.admit catalog boundary ledger actualEffect.asset)
    |>.mapError .knowledge
  return (receipt, updated)

end CedarPooSpec.Governance.Personnel
