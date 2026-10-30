import CedarPooSpec.Gateway

namespace CedarPooSpec.GatewayTest
open Cedar.Spec Cedar.Validation Cedar.Data

def userType : EntityType := ⟨"User", []⟩
def endpointType : EntityType := ⟨"Endpoint", []⟩
def actionType : EntityType := ⟨"Action", []⟩
def user : EntityUID := ⟨userType, "agent"⟩
def endpoint : EntityUID := ⟨endpointType, "service"⟩
def action (name : String) : EntityUID := ⟨actionType, name⟩
def entityEntry : EntitySchemaEntry := .standard ⟨Set.empty, Map.empty, none⟩
def actionEntry : ActionSchemaEntry :=
  ⟨Set.make [userType], Set.make [endpointType], Set.empty,
    Map.make [("allowed", .required (.bool .anyBool))]⟩
def schema : Schema :=
  ⟨Map.make [(userType, entityEntry), (endpointType, entityEntry)],
    Map.make [(action "invoke", actionEntry), (action "tool", actionEntry)]⟩
def entities : Entities := Map.make [
  (user, { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }),
  (endpoint, { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }),
  (action "invoke", actionSchemaEntryToEntityData actionEntry),
  (action "tool", actionSchemaEntryToEntityData actionEntry)]

def request (name : String) (allowed : Bool) : Request :=
  ⟨user, action name, endpoint, Map.make [("allowed", .prim (.bool allowed))]⟩
def permitPolicy : Policy :=
  { id := "gateway-permit", effect := .permit,
    principalScope := .principalScope .any, actionScope := .actionScope .any,
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := .getAttr (.var .context) "allowed" }] }
def denyPolicy : Policy :=
  { permitPolicy with id := "gateway-freeze", effect := .forbid, condition := [] }
def model : PolicyModules.Model :=
  { modules := [
    { name := "base", edits := [.extend permitPolicy] },
    { name := "restricted", parentOrders := [["base"]], edits := [.extend denyPolicy] }] }
def replacedModel : PolicyModules.Model :=
  { modules := [{ name := "base", edits := [.extend { denyPolicy with id := permitPolicy.id }] }] }

-- Equal active policy bodies do not imply identical declaration provenance.
def sourceChangedModel : PolicyModules.Model :=
  { modules := model.modules ++ [{ name := "new-owner", parentOrders := [["base"]] }] }

def scope : Gateway.Scope :=
  { originalRoot := "task", claim := "step", canonicalOperation := "task/step",
    profile := "gateway", budgetDomain := "account", historyDomain := "history",
    schemaIdentity := "schema", sourceCut := "source-1", moduleClosure := "modules-1",
    projectionClosure := "projection-1" }
def context : Gateway.Context := ⟨scope, 1, 1, 1, 1⟩
def profile : Gateway.Profile := ⟨"gateway", ["source", "budget", "history"]⟩
def checks : List Gateway.Assessment := profile.requiredChecks.map (fun name => ⟨name, .satisfied⟩)
def prepared (name : String := "invoke") : Gateway.Prepared String Bool request :=
  { operationId := ⟨scope.canonicalOperation⟩, operation := ⟨name, true⟩,
    policy := ⟨"base", [permitPolicy]⟩, schema, context, profile, sourceModules := model.modules }

def authorize (value : Gateway.Prepared String Bool request := prepared)
    (currentModel : PolicyModules.Model := model) (currentContext := context)
    (assessments := checks) (effect := "invoke") (state := true) :=
  Gateway.authorize value currentModel effect state currentContext assessments entities

def grants (id := "approval") : Admission.AuthorityLedger String :=
  ⟨[⟨id, "invoke", 1, 0⟩]⟩
def consume (operations : Admission.OperationLedger) (authorities : Admission.AuthorityLedger String)
    (id : String) : Option (Gateway.Consumed String) :=
  (authorize).toOption.bind fun receipt =>
    (Gateway.consumeAdmission receipt operations authorities id).toOption

end CedarPooSpec.GatewayTest
