import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson

/-!
Two Cedar namespaces share a policy: an organization owns users and actions,
while a data namespace owns documents and their enumerated classifications.
The POO overlay narrows a published grant to public documents.
-/

namespace CedarPooSpec.NamespacedEnumExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules

def userType : EntityType := ⟨"User", ["Org"]⟩
def actionType : EntityType := ⟨"Action", ["Org"]⟩
def documentType : EntityType := ⟨"Document", ["Data"]⟩
def classificationType : EntityType := ⟨"Classification", ["Data"]⟩

def alice : EntityUID := ⟨userType, "alice"⟩
def publicDoc : EntityUID := ⟨documentType, "public"⟩
def restrictedDoc : EntityUID := ⟨documentType, "restricted"⟩
def publicClass : EntityUID := ⟨classificationType, "public"⟩
def restrictedClass : EntityUID := ⟨classificationType, "restricted"⟩
def readAction : EntityUID := ⟨actionType, "read"⟩

def schema : Schema :=
  ⟨Map.make [
    (userType, .standard ⟨Set.empty, Map.empty, none⟩),
    (documentType, .standard ⟨Set.empty,
      Map.make [("classification", .required (.entity classificationType))], none⟩),
    (classificationType, .enum (Set.make ["public", "restricted"]))],
    Map.make [(readAction, ⟨Set.make [userType],
      Set.make [documentType], Set.empty, Map.empty⟩)]⟩

def data (attrs : Map String Value := Map.empty) : EntityData :=
  { attrs, ancestors := Set.empty, tags := Map.empty }

def documentData (classification : EntityUID) : EntityData :=
  data (Map.make [("classification", .prim (.entityUID classification))])

def entities : Entities := Map.make [
  (alice, data),
  (publicDoc, documentData publicClass),
  (restrictedDoc, documentData restrictedClass),
  (publicClass, data), (restrictedClass, data),
  (readAction, data)]

def publishedPolicy : Policy :=
  { id := "read-document", effect := .permit,
    principalScope := .principalScope (.is userType),
    actionScope := .actionScope (.eq readAction),
    resourceScope := .resourceScope (.is documentType),
    condition := [] }

def publicOnly : Expr :=
  .binaryApp .eq (.getAttr (.var .resource) "classification")
    (.lit (.entityUID publicClass))

def scopedPolicy : Policy :=
  { publishedPolicy with condition := [{ kind := .when, body := publicOnly }] }

def model : Model :=
  { modules := [
    { name := "Published", edits := [.extend publishedPolicy] },
    { name := "Scoped", parentOrders := [["Published"]],
      edits := [.overlay scopedPolicy] }] }

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

def request (resource : EntityUID) : Request :=
  ⟨alice, readAction, resource, Map.empty⟩

def cases : List (String × String × Request × Decision) := [
  ("published-public", "Published", request publicDoc, .allow),
  ("published-restricted", "Published", request restrictedDoc, .allow),
  ("scoped-public", "Scoped", request publicDoc, .allow),
  ("scoped-restricted", "Scoped", request restrictedDoc, .deny)]

def decisionsExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.NamespacedEnumExample.model CedarPooSpec.NamespacedEnumExample.schema :=
      CedarPooSpec.NamespacedEnumExample.program) : Bool := cases.all fun (_, root, req, expected) =>
  match programContext.response root req entities with
  | .error _ => false
  | .ok response =>
      response.decision == expected && response.erroringPolicies.isEmpty

theorem decisionsExactFully : decisionsExact = true := by native_decide

def schemaValidationExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.NamespacedEnumExample.model CedarPooSpec.NamespacedEnumExample.schema :=
      CedarPooSpec.NamespacedEnumExample.program) : Bool :=
  ["Published", "Scoped"].all fun root => (programContext.at root).isOk

theorem schemaValidationFully : schemaValidationExact = true := by native_decide

end CedarPooSpec.NamespacedEnumExample
