import CedarPooSpec.Gateway.OAuth
import CedarPooSpec.Governance.Veto

/-!
Reusable Cedar policy objects for an application consuming patient-scoped FHIR
resources through an intermediary. A separate FHIR implementation and Host
project verified facts into Cedar requests. This module only composes Cedar
application controls; it does not parse FHIR or interpret its specification.
-/

namespace CedarPooSpec.Vertical.Health.FHIR

open Cedar.Spec CedarPooSpec.PolicyModules CedarPooSpec.Governance

private def attr (source : Var) (name : String) : Expr :=
  .getAttr (.var source) name
private def context (name : String) : Expr := attr .context name
private def equals (left right : Expr) : Expr := .binaryApp .eq left right
private def literal (value : String) : Expr := .lit (.string value)
private def negated (body : Expr) : Expr := .unaryApp .not body

/-- A patient-scoped application read with an explicit purpose and resource class. -/
structure ResourceRead where
  policyId : PolicyID
  action : EntityUID
  principalKind : String
  resourceKind : String
  purpose : String
  kindAttribute : String := "kind"
  purposeFact : String := "purpose"

def ResourceRead.policy (control : ResourceRead) : Policy :=
  { id := control.policyId, effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope (.eq control.action),
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := (
      .and (equals (attr .principal control.kindAttribute)
        (literal control.principalKind))
        (.and (equals (attr .resource control.kindAttribute)
          (literal control.resourceKind))
          (equals (context control.purposeFact) (literal control.purpose)))) }] }

def ResourceRead.introduce (control : ResourceRead) : Edit :=
  .extend control.policy

/-- One patient binding shared by every action selected by the application. -/
structure PatientBoundary where
  policyId : PolicyID
  actionScope : ActionScope
  principalPatientAttribute : String := "patient"
  resourcePatientAttribute : String := "patient"
  subjectPatientFact : String := "subjectPatient"

def PatientBoundary.control (boundary : PatientBoundary) : Veto :=
  { policyId := boundary.policyId, actionScope := boundary.actionScope,
    denyWhen := negated <|
      .and (equals (attr .principal boundary.principalPatientAttribute)
        (context boundary.subjectPatientFact))
        (equals (attr .resource boundary.resourcePatientAttribute)
          (context boundary.subjectPatientFact)) }

/-- Host-projected OAuth, session, and inactivity facts for one read action. -/
structure ConsumerSession where
  policyId : PolicyID
  action : EntityUID
  oauthActiveFact : String := "oauthActive"
  sessionActiveFact : String := "sessionActive"
  inactivityWindowFact : String := "withinInactivityWindow"

def ConsumerSession.control (session : ConsumerSession) : Veto :=
  { policyId := session.policyId,
    actionScope := .actionScope (.eq session.action),
    denyWhen := .or (negated (context session.oauthActiveFact))
      (.or (negated (context session.sessionActiveFact))
        (negated (context session.inactivityWindowFact))) }

/-- Revocation applies to selected data operations, leaving cleanup selectable. -/
structure RevocableUse where
  policyId : PolicyID
  actions : List EntityUID
  accessActiveFact : String := "appAccessActive"

def RevocableUse.control (access : RevocableUse) : Veto :=
  { policyId := access.policyId,
    actionScope := .actionInAny access.actions,
    denyWhen := negated (context access.accessActiveFact) }

/-- Apply current Host-verified OAuth evidence to the existing resource policy.
The caller supplies the observation from the actual deciding view. -/
def withOAuth (base : CedarPooSpec.ZeroTrust.Framework E V)
    (observe : E → V → CedarPooSpec.Gateway.OAuth.CurrentUse) :=
  CedarPooSpec.Gateway.OAuth.strengthen base observe

end CedarPooSpec.Vertical.Health.FHIR
