import CedarPooSpec.Functional.Capabilities
import Examples.Governance.AttestedDataAccess
import CedarPooSpec.PolicyJson
import CedarPooSpec.Admission.SourceNetwork

/-!
A network-boundary revision of the attested-data scenario. An upstream gateway
projects the verified source IP as a Cedar extension value; this model does
not authenticate the address or enforce the returned decision.
-/

namespace CedarPooSpec.TrustedNetworkDataAccessExample

open Cedar.Spec Cedar.Validation Cedar.Data CedarPooSpec.PolicyModules
open CedarPooSpec.AttestedDataAccessExample
open CedarPooSpec.AttestedManifest
open CedarPooSpec.Admission

def networkControl (range : String) : SourceNetwork :=
  { policyId := "network-boundary",
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq queryAction),
    resourceScope := .resourceScope .any,
    acceptedRange := range }

/-- A named network boundary owns its parent and accepted CIDR. Narrowing
    the same policy object overlays its body without copying its ancestor. -/
structure NetworkBoundary where
  name : String
  parent : String
  control : SourceNetwork
  change : SourceNetwork.Change

def NetworkBoundary.edit (boundary : NetworkBoundary) : Edit :=
  boundary.control.edit boundary.change

def corporate : NetworkBoundary :=
  ⟨"CorporateNetwork", Root.strengthened.name, networkControl "10.0.0.0/8", .introduce⟩
def enclave : NetworkBoundary :=
  ⟨"EnclaveNetwork", "CorporateNetwork", networkControl "10.20.0.0/16", .revise⟩
def boundaries : List NetworkBoundary := [corporate, enclave]

def networkModelResult : Except LeanPoo.C4.Error Model :=
  boundaries.foldlM (fun current boundary =>
    current.extend boundary.name boundary.parent [boundary.edit])
    CedarPooSpec.AttestedDataAccessExample.model

def networkModel : Model := networkModelResult.toOption.get (by native_decide)

theorem boundaryObjectProvenance :
    ((networkModel.compileWithProvenance "EnclaveNetwork").toOption.get
      (by native_decide)).any (fun compiled =>
        compiled.policy.id == "network-boundary" &&
        compiled.introducedBy == corporate.name &&
        compiled.lastEditedBy == enclave.name) = true := by native_decide

def networkContextType : RecordType := Map.make
  (contextType.toList ++ [("sourceIp", .required (.ext .ipAddr))])

def networkActionEntry : ActionSchemaEntry :=
  ⟨Set.make [workerType], Set.make [datasetType], Set.empty, networkContextType⟩

def networkSchema : Schema :=
  ⟨schemaWithClassification.ets, Map.make [(queryAction, networkActionEntry)]⟩

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def networkProgram : CedarPooSpec.Functional.Program networkModel networkSchema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    networkModel networkSchema (networkModel.modules.map (·.name)) (by native_decide)

def networkEntities : Entities := Map.make
  (entities.toList.map fun (uid, data) =>
    if uid == queryAction then
      (uid, actionSchemaEntryToEntityData networkActionEntry)
    else (uid, data))

def officeIp : IPAddr :=
  (Ext.IPAddr.ip "10.20.1.7").get (by native_decide)
def otherCorporateIp : IPAddr :=
  (Ext.IPAddr.ip "10.30.1.7").get (by native_decide)
def outsideIp : IPAddr :=
  (Ext.IPAddr.ip "198.51.100.7").get (by native_decide)

def requestWithIp (dataset : EntityUID) (facts : Facts) (ip : IPAddr) : Request :=
  let original := request dataset facts
  let context := Map.make
    (original.context.toList ++ [("sourceIp", .ext (.ipaddr ip))])
  ⟨original.principal, original.action, original.resource, context⟩

def cases : List (String × String × Request × Decision) := [
  ("corporate-office", "CorporateNetwork",
    requestWithIp customerDataset {} officeIp, .allow),
  ("corporate-other-subnet", "CorporateNetwork",
    requestWithIp customerDataset {} otherCorporateIp, .allow),
  ("corporate-outside", "CorporateNetwork",
    requestWithIp customerDataset {} outsideIp, .deny),
  ("enclave-office", "EnclaveNetwork",
    requestWithIp customerDataset {} officeIp, .allow),
  ("enclave-other-subnet", "EnclaveNetwork",
    requestWithIp customerDataset {} otherCorporateIp, .deny),
  ("enclave-outside", "EnclaveNetwork",
    requestWithIp customerDataset {} outsideIp, .deny),
  ("enclave-stale-attestation", "EnclaveNetwork",
    requestWithIp customerDataset { attestationFresh := false } officeIp, .deny),
  ("enclave-owner-rejected", "EnclaveNetwork",
    requestWithIp customerDataset { ownerApproved := false } officeIp, .deny),
  ("enclave-other-project", "EnclaveNetwork",
    requestWithIp financeDataset {} officeIp, .deny)]

def decisionsExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.TrustedNetworkDataAccessExample.networkModel CedarPooSpec.TrustedNetworkDataAccessExample.networkSchema :=
      CedarPooSpec.TrustedNetworkDataAccessExample.networkProgram) : Bool :=
  cases.all fun (_, root, req, expected) =>
    match programContext.response root req networkEntities with
    | .error _ => false
    | .ok response =>
        response.decision == expected && response.erroringPolicies.isEmpty

theorem decisionsExactFully : decisionsExact = true := by native_decide

def policyRevision : Revision :=
  (networkModel.compileRevision "CorporateNetwork" "EnclaveNetwork").toOption.get
    (by native_decide)

theorem onlyNetworkBodyChanged :
    policyRevision.changedPolicyIds = ["network-boundary"] := by native_decide

theorem validatedRevisions :
    (validate policyRevision.beforePolicies networkSchema).isOk = true ∧
    (validate policyRevision.afterPolicies networkSchema).isOk = true := by
  native_decide

def earlierRootAllowsExternal : Bool :=
  match networkModel.compile Root.strengthened.name with
  | .error _ => false
  | .ok policies =>
      (isAuthorized (requestWithIp customerDataset {} outsideIp)
        networkEntities policies).decision == .allow &&
      (isAuthorized (requestWithIp customerDataset {} outsideIp)
        networkEntities policyRevision.afterPolicies).decision == .deny

theorem externalAccessClosed : earlierRootAllowsExternal = true := by native_decide

end CedarPooSpec.TrustedNetworkDataAccessExample
