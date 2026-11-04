import CedarPooSpec.Gateway.OAuth
import CedarPooSpec.PolicyJson

/-! Reusable AgentCore Gateway projection. Business-specific Cedar rules and
authenticated AWS runtime evidence remain with consumers. -/

namespace CedarPooSpec.Platform.AWS.AgentCore

open Cedar.Spec Cedar.Data Cedar.Validation

def userType : EntityType := ⟨"OAuthUser", ["AgentCore"]⟩
def gatewayType : EntityType := ⟨"Gateway", ["AgentCore"]⟩
def actionType : EntityType := ⟨"Action", ["AgentCore"]⟩

def user (name : String) : EntityUID := ⟨userType, name⟩
def gateway (name : String) : EntityUID := ⟨gatewayType, name⟩
def action (name : String) : EntityUID := ⟨actionType, name⟩

def actionEntryFor (principals : List EntityType) (context : RecordType) :
    ActionSchemaEntry :=
  ⟨Set.make principals, Set.make [gatewayType], Set.empty, context⟩

def actionEntry (context : RecordType) : ActionSchemaEntry :=
  actionEntryFor [userType] context

def entityData (tags : List (String × Value) := []) : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.make tags }

def gatewayPolicy (id : String) (effect : Effect)
    (principals : PrincipalScope) (gatewayUID : EntityUID)
    (actions : ActionScope) (conditions : Conditions := []) : Policy :=
  { id, effect,
    principalScope := principals,
    actionScope := actions,
    resourceScope := .resourceScope (.eq gatewayUID),
    condition := conditions }

def scopedPolicy (id : String) (effect : Effect) (gatewayUID : EntityUID)
    (actions : ActionScope) (conditions : Conditions := []) : Policy :=
  gatewayPolicy id effect (.principalScope (.is userType)) gatewayUID actions conditions

/-- Apply current Host-verified OAuth evidence to the existing resource policy.
The caller supplies the observation from the actual deciding view. -/
def withOAuth (base : CedarPooSpec.ZeroTrust.Framework E V)
    (observe : E → V → CedarPooSpec.Gateway.OAuth.CurrentUse) :=
  CedarPooSpec.Gateway.OAuth.strengthen base observe

end CedarPooSpec.Platform.AWS.AgentCore
