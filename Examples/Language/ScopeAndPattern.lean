import CedarPooSpec.Functional.Capabilities
import CedarPooSpec.PolicyJson

/-!
Concrete Cedar syntax probe based on the documented `is`, `is ... in`,
`like`, and nested `has` JSON forms. Identifiers and email addresses are fictive.
-/

namespace CedarPooSpec.ScopeAndPatternExample

open Cedar.Spec Cedar.Data Cedar.Validation CedarPooSpec.PolicyModules

def userType : EntityType := ⟨"User", []⟩
def groupType : EntityType := ⟨"Group", []⟩
def documentType : EntityType := ⟨"Document", []⟩
def folderType : EntityType := ⟨"Folder", []⟩
def actionType : EntityType := ⟨"Action", []⟩

def alice : EntityUID := ⟨userType, "alice"⟩
def bob : EntityUID := ⟨userType, "bob"⟩
def staff : EntityUID := ⟨groupType, "staff"⟩
def publicFolder : EntityUID := ⟨folderType, "public"⟩
def publicDocument : EntityUID := ⟨documentType, "public"⟩
def privateDocument : EntityUID := ⟨documentType, "private"⟩
def viewAction : EntityUID := ⟨actionType, "view"⟩

def schema : Schema :=
  ⟨Map.make [
    (userType, .standard ⟨Set.make [groupType],
      Map.make [("email", .required .string)], none⟩),
    (groupType, .standard ⟨Set.empty, Map.empty, none⟩),
    (documentType, .standard ⟨Set.make [folderType],
      Map.make [("meta", .required (.record
        (Map.make [("tag", .required .string)])))], none⟩),
    (folderType, .standard ⟨Set.empty, Map.empty, none⟩)],
   Map.make [(viewAction, ⟨Set.make [userType],
     Set.make [documentType], Set.empty, Map.empty⟩)]⟩

def entityData (attrs : Map String Value) (ancestors : Set EntityUID := Set.empty) :
    EntityData :=
  { attrs, ancestors, tags := Map.empty }

def userData (email : String) (ancestors : Set EntityUID := Set.empty) : EntityData :=
  entityData (Map.make [("email", .prim (.string email))]) ancestors

def documentData (tag : String) (ancestors : Set EntityUID := Set.empty) : EntityData :=
  entityData (Map.make [("meta", .record (Map.make [
    ("tag", .prim (.string tag))]))]) ancestors

def entities : Entities := Map.make [
  (alice, userData "alice@example.org" (Set.make [staff])),
  (bob, userData "bob@example.org"),
  (staff, entityData Map.empty),
  (publicFolder, entityData Map.empty),
  (publicDocument, documentData "public" (Set.make [publicFolder])),
  (privateDocument, documentData "private"),
  (viewAction, entityData Map.empty)]

def emailPattern : Pattern := [.star, .justChar '@', .justChar 'e',
  .justChar 'x', .justChar 'a', .justChar 'm', .justChar 'p',
  .justChar 'l', .justChar 'e', .justChar '.', .justChar 'o',
  .justChar 'r', .justChar 'g']

def emailMatches : Expr :=
  .unaryApp (.like emailPattern) (.getAttr (.var .principal) "email")

def publishedBody : Expr :=
  .and emailMatches (.unaryApp (.is userType) (.var .principal))

def scopedBody : Expr :=
  .and emailMatches (.extHasAttr (.var .resource) "meta" ["tag"])

def publishedPolicy : Policy :=
  { id := "document-view", effect := .permit,
    principalScope := .principalScope (.is userType),
    actionScope := .actionScope (.eq viewAction),
    resourceScope := .resourceScope (.is documentType),
    condition := [{ kind := .when, body := publishedBody }] }

def scopedPolicy : Policy :=
  { publishedPolicy with
    principalScope := .principalScope (.isMem userType staff),
    resourceScope := .resourceScope (.isMem documentType publicFolder),
    condition := [{ kind := .when, body := scopedBody }] }

def model : Model :=
  { modules := [
    { name := "Published", edits := [.extend publishedPolicy] },
    { name := "Scoped", parentOrders := [["Published"]],
      edits := [.overlay scopedPolicy] }] }

/-- Checked immutable policy context; current request inputs are supplied at consumption. -/
protected def program : CedarPooSpec.Functional.Program model schema :=
  CedarPooSpec.Functional.deferProgram CedarPooSpec.Functional.standard
    model schema (model.modules.map (·.name)) (by native_decide)

def request (principal resource : EntityUID) : Request :=
  ⟨principal, viewAction, resource, Map.empty⟩

def cases : List (String × String × Request × Decision) := [
  ("published-public", "Published", request alice publicDocument, .allow),
  ("published-private", "Published", request alice privateDocument, .allow),
  ("scoped-public", "Scoped", request alice publicDocument, .allow),
  ("scoped-private", "Scoped", request alice privateDocument, .deny),
  ("scoped-nonmember", "Scoped", request bob publicDocument, .deny)]

def decisionsExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.ScopeAndPatternExample.model CedarPooSpec.ScopeAndPatternExample.schema :=
      CedarPooSpec.ScopeAndPatternExample.program) : Bool := cases.all fun (_, root, req, expected) =>
  match programContext.response root req entities with
  | .error _ => false
  | .ok response =>
      response.decision == expected && response.erroringPolicies.isEmpty

theorem decisionsExactFully : decisionsExact = true := by native_decide

def schemaValidationExact
    (programContext : CedarPooSpec.Functional.Program CedarPooSpec.ScopeAndPatternExample.model CedarPooSpec.ScopeAndPatternExample.schema :=
      CedarPooSpec.ScopeAndPatternExample.program) : Bool :=
  ["Published", "Scoped"].all fun root => (programContext.at root).isOk

theorem schemaValidationFully : schemaValidationExact = true := by native_decide

end CedarPooSpec.ScopeAndPatternExample
