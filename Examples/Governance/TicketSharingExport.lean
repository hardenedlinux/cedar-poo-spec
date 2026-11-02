import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.Functional.CompilationJson
import CedarPooSpec.PolicyJson
import Examples.Governance.TicketSharing

/-! Machine-readable cases computed from the Lean POO/Cedar source objects. -/

namespace CedarPooSpec.TicketSharingExport

open CedarPooSpec.TicketSharingExample

theorem unsupportedScopeRejected :
    (match PolicyJson.policy
      { Cedar.Spec.Policy.allowAll with
        actionScope := .actionScope (.is actionType) } with
     | .error (.unsupportedScope _) => true
     | _ => false) = true := by
  native_decide

theorem duplicateIdsRejected :
    (match PolicyJson.policySet [Cedar.Spec.Policy.allowAll,
      Cedar.Spec.Policy.allowAll] with
     | .error (.duplicatePolicyId _) => true
     | _ => false) = true := by
  native_decide

private def case {model : CedarPooSpec.PolicyModules.Model}
    (source : CedarPooSpec.Functional.Program model schema) (name root : String)
    (req : Cedar.Spec.Request) (store : Cedar.Spec.Entities) :
    Except String CedarPooSpec.Transport.Case :=
  source.case name root.toLower root req store

def manifest (source : CedarPooSpec.Functional.Program model schema ×
    CedarPooSpec.Functional.Program expandedModel schema := (CedarPooSpec.TicketSharingExample.program, CedarPooSpec.TicketSharingExample.expandedProgram)) : Except String CedarPooSpec.Transport.Manifest := do
  let baselineCases ← List.mapM (fun (name, root, req, store) =>
    case source.1 name root req store) [
    ("published-alice", "Published", request alice ticketA false, entities),
    ("posture-untrusted", "Posture", request alice ticketA false, entities),
    ("posture-trusted", "Posture", request alice ticketA true, entities),
    ("posture-viewer", "Posture", request bob ticketA false, entities),
    ("posture-closed", "Posture", request alice ticketA true, closedEntities),
    ("revoked-bob", "Revoked", request bob ticketB true, entities),
    ("revoked-viewer", "Revoked", request bob ticketA false, entities)]
  let newGrant ← case source.2 "expanded-alice" "Expanded"
    (request alice ticketB true) entities
  let stillRevoked ← case source.2 "expanded-bob" "Expanded"
    (request bob ticketB true) entities
  return { cases := (baselineCases ++ [newGrant, stillRevoked]) }

end CedarPooSpec.TicketSharingExport
