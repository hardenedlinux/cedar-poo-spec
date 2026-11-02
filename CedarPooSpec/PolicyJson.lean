import CedarPooSpec.PolicyPreparation
import CedarPooSpec.Transport.SourceTable
import Cedar.Spec.Entities
import Cedar.Spec.Request
import Cedar.Spec.Authorizer
import Cedar.Spec.Template
import Cedar.Validation.Validator
import Cedar.Validation.EnvironmentValidator
import Cedar.Thm.Authorization
import Lean.Data.Json

/-!
Export the concrete subset of Cedar's Lean policy AST to Cedar's documented
JSON policy-set format. Unsupported abstract forms fail before deployment.
-/

namespace CedarPooSpec.PolicyJson

open Cedar.Spec

inductive Error where
  | unsupportedScope (policyId : PolicyID)
  | unsupportedExpression (policyId : PolicyID)
  | expressionDepthExceeded (policyId : PolicyID)
  | duplicatePolicyId (policyId : PolicyID)
  | duplicateRecordKey (policyId : PolicyID)
  | duplicateEntityAttribute
  | duplicateTemplateId
  | unlinkedTemplateId (templateId : TemplateID)
  | duplicateTemplateLinkId
  | duplicateSlotBinding
  | invalidTemplateLink (message : String)
  | incompleteEntityAncestors (uid : EntityUID)
  | unsupportedValue
  | valueDepthExceeded
  deriving Repr, BEq

private def obj (fields : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj fields

-- Cedar maps normally present canonical ordered fields, but their public raw
-- constructor permits arbitrary lists. Certify the adjacent-key fast path and
-- retain the original complete duplicate decision for every unordered input.
private def ascendingKeysFrom (previous : String) : List (String × α) → Bool
  | [] => true
  | (key, _) :: rest => decide (previous < key) && ascendingKeysFrom key rest

private theorem ascendingKeysFrom_sound (fields : List (String × α)) (previous : String)
    (ordered : ascendingKeysFrom previous fields = true) :
    (∀ field ∈ fields, previous < field.1) ∧ (fields.map Prod.fst).Nodup := by
  induction fields generalizing previous with
  | nil => exact ⟨by simp, by simp⟩
  | cons field rest ih =>
    have parts : previous < field.1 ∧ ascendingKeysFrom field.1 rest = true := by
      simpa [ascendingKeysFrom] using ordered
    obtain ⟨larger, unique⟩ := ih field.1 parts.2
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, unique⟩⟩
    · intro next member
      rcases List.mem_cons.mp member with same | member
      · subst next; exact parts.1
      · exact String.lt_trans parts.1 (larger next member)
    · intro member
      obtain ⟨next, member, same⟩ := List.mem_map.mp member
      have less := larger next member
      rw [same] at less
      exact String.lt_irrefl _ less

/-- Linear adjacent checks for ordered fields; the original exact decision is
used for arbitrary order. No key list or hash table is allocated on a hit. -/
def uniqueRecordKeys (fields : List (String × α)) : Bool :=
  match fields with
  | [] => true
  | (key, _) :: rest =>
    if ascendingKeysFrom key rest then true else decide (fields.map Prod.fst).Nodup

theorem uniqueRecordKeys_eq (fields : List (String × α)) :
    uniqueRecordKeys fields = decide (fields.map Prod.fst).Nodup := by
  cases fields with
  | nil => rfl
  | cons field rest =>
    by_cases ordered : ascendingKeysFrom field.1 rest = true
    · have facts := ascendingKeysFrom_sound rest field.1 ordered
      have unique : (field :: rest).map Prod.fst |>.Nodup := by
        refine List.nodup_cons.mpr ⟨?_, facts.2⟩
        intro member
        obtain ⟨next, member, same⟩ := List.mem_map.mp member
        have less := facts.1 next member
        rw [same] at less
        exact String.lt_irrefl _ less
      simpa only [uniqueRecordKeys, ordered, ↓reduceIte] using
        (decide_eq_true unique).symm
    · simp [uniqueRecordKeys, ordered]

def entity (uid : EntityUID) : Lean.Json :=
  obj [("type", Lean.toJson (toString uid.ty)), ("id", Lean.toJson uid.eid)]

private def scope : Scope → Except Error Lean.Json
  | .any => .ok (obj [("op", Lean.toJson "All")])
  | .eq uid => .ok (obj [("op", Lean.toJson "=="), ("entity", entity uid)])
  | .mem uid => .ok (obj [("op", Lean.toJson "in"), ("entity", entity uid)])
  | .is ty => .ok (obj [("op", Lean.toJson "is"),
      ("entity_type", Lean.toJson (toString ty))])
  | .isMem ty uid => .ok (obj [("op", Lean.toJson "is"),
      ("entity_type", Lean.toJson (toString ty)),
      ("in", obj [("entity", entity uid)])])

private def actionScope (id : PolicyID) : ActionScope → Except Error Lean.Json
  | .actionScope (.is _) => .error (.unsupportedScope id)
  | .actionScope (.isMem _ _) => .error (.unsupportedScope id)
  | .actionScope s => scope s
  | .actionInAny uids =>
      .ok (obj [("op", Lean.toJson "in"), ("entities", Lean.toJson (uids.map entity))])

private def primitive : Prim → Lean.Json
  | .bool value => Lean.toJson value
  | .int value => Lean.toJson value.toInt
  | .string value => Lean.toJson value
  | .entityUID uid => obj [("__entity", entity uid)]

private def varName : Var → String
  | .principal => "principal"
  | .action => "action"
  | .resource => "resource"
  | .context => "context"

private def binaryName : BinaryOp → String
  | .eq => "=="
  | .mem => "in"
  | .hasTag => "hasTag"
  | .getTag => "getTag"
  | .less => "<"
  | .lessEq => "<="
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .contains => "contains"
  | .containsAll => "containsAll"
  | .containsAny => "containsAny"

private def pair (name : String) (left right : Lean.Json) : Lean.Json :=
  obj [(name, obj [("left", left), ("right", right)])]

private def unary (name : String) (arg : Lean.Json) : Lean.Json :=
  obj [(name, obj [("arg", arg)])]

private def patternElement : PatElem → Lean.Json
  | .star => Lean.toJson "Wildcard"
  | .justChar char => obj [("Literal", Lean.toJson (String.ofList [char]))]

private def extensionFunction : ExtFun → Option (String × Nat)
  | .decimal => some ("decimal", 1)
  | .lessThan => some ("lessThan", 2)
  | .lessThanOrEqual => some ("lessThanOrEqual", 2)
  | .greaterThan => some ("greaterThan", 2)
  | .greaterThanOrEqual => some ("greaterThanOrEqual", 2)
  | .ip => some ("ip", 1)
  | .isIpv4 => some ("isIpv4", 1)
  | .isIpv6 => some ("isIpv6", 1)
  | .isLoopback => some ("isLoopback", 1)
  | .isMulticast => some ("isMulticast", 1)
  | .isInRange => some ("isInRange", 2)
  | .datetime => some ("datetime", 1)
  | .duration => some ("duration", 1)
  | .offset => some ("offset", 2)
  | .durationSince => some ("durationSince", 2)
  | .toDate => some ("toDate", 1)
  | .toTime => some ("toTime", 1)
  | .toMilliseconds => some ("toMilliseconds", 1)
  | .toSeconds => some ("toSeconds", 1)
  | .toMinutes => some ("toMinutes", 1)
  | .toHours => some ("toHours", 1)
  | .toDays => some ("toDays", 1)

private def expressionFuel (id : PolicyID) : Nat → Cedar.Spec.Expr → Except Error Lean.Json
  | 0, _ => .error (.expressionDepthExceeded id)
  | _fuel + 1, .lit value => .ok (obj [("Value", primitive value)])
  | _fuel + 1, .var value => .ok (obj [("Var", Lean.toJson (varName value))])
  | fuel + 1, .and left right => do
      return pair "&&" (← expressionFuel id fuel left) (← expressionFuel id fuel right)
  | fuel + 1, .or left right => do
      return pair "||" (← expressionFuel id fuel left) (← expressionFuel id fuel right)
  | fuel + 1, .binaryApp op left right => do
      return pair (binaryName op) (← expressionFuel id fuel left) (← expressionFuel id fuel right)
  | fuel + 1, .getAttr left attr => do
      return obj [(".", obj [("left", ← expressionFuel id fuel left), ("attr", Lean.toJson attr)])]
  | fuel + 1, .hasAttr left attr => do
      return obj [("has", obj [("left", ← expressionFuel id fuel left), ("attr", Lean.toJson attr)])]
  | fuel + 1, .extHasAttr left attr attrs => do
      return obj [("has", obj [("left", ← expressionFuel id fuel left),
        ("attr", Lean.toJson (attr :: attrs))])]
  | fuel + 1, .unaryApp .not arg => do return unary "!" (← expressionFuel id fuel arg)
  | fuel + 1, .unaryApp .neg arg => do return unary "neg" (← expressionFuel id fuel arg)
  | fuel + 1, .unaryApp .isEmpty arg => do return unary "isEmpty" (← expressionFuel id fuel arg)
  | fuel + 1, .unaryApp (.is ty) arg => do
      return obj [("is", obj [("left", ← expressionFuel id fuel arg),
        ("entity_type", Lean.toJson (toString ty))])]
  | fuel + 1, .unaryApp (.like pattern) arg => do
      return obj [("like", obj [("left", ← expressionFuel id fuel arg),
        ("pattern", Lean.toJson (pattern.map patternElement))])]
  | fuel + 1, .ite cond yes no => do
      return obj [("if-then-else", obj [
        ("if", ← expressionFuel id fuel cond), ("then", ← expressionFuel id fuel yes),
        ("else", ← expressionFuel id fuel no)])]
  | fuel + 1, .set members => do
      return obj [("Set", Lean.toJson (← members.mapM (expressionFuel id fuel)))]
  | fuel + 1, .record fields => do
      if !(uniqueRecordKeys fields) then
        throw (.duplicateRecordKey id)
      let fields ← fields.mapM fun (key, value) => do
        return (key, ← expressionFuel id fuel value)
      return obj [("Record", obj fields)]
  | fuel + 1, .call fn args => do
      let some (name, arity) := extensionFunction fn
        | throw (.unsupportedExpression id)
      if args.length != arity then
        throw (.unsupportedExpression id)
      return obj [(name, Lean.toJson (← args.mapM (expressionFuel id fuel)))]

private def expression (id : PolicyID) (expr : Cedar.Spec.Expr) : Except Error Lean.Json :=
  expressionFuel id 1024 expr

private def condition (id : PolicyID) (c : Condition) : Except Error Lean.Json := do
  return obj [("kind", Lean.toJson (match c.kind with
    | .when => "when"
    | .unless => "unless")), ("body", ← expression id c.body)]

/-- Serialize a materialized Lean policy to Cedar's public JSON form. -/
def policy (value : Policy) : Except Error Lean.Json := do
  return obj [
    ("effect", Lean.toJson (match value.effect with
      | .permit => "permit"
      | .forbid => "forbid")),
    ("principal", ← scope value.principalScope.scope),
    ("action", ← actionScope value.id value.actionScope),
    ("resource", ← scope value.resourceScope.scope),
    ("conditions", Lean.toJson (← value.condition.mapM (condition value.id)))]

private def staticEntries (policies : Policies) :
    Except Error (List (String × Lean.Json)) := do
  let mut entries : List (String × Lean.Json) := []
  for value in policies do
    if entries.any (fun entry => entry.1 == value.id) then
      throw (.duplicatePolicyId value.id)
    entries := entries ++ [(value.id, ← policy value)]
  return entries

/-- A materialized policy set with no templates or links. -/
def policySet (policies : Policies) : Except Error Lean.Json := do
  let entries ← staticEntries policies
  return obj [
    ("staticPolicies", obj entries),
    ("templates", obj []),
    ("templateLinks", Lean.toJson (#[] : Array Lean.Json))]

private def entityOrSlot : EntityUIDOrSlot → String × Lean.Json
  | .entityUID uid => ("entity", entity uid)
  | .slot id => ("slot", Lean.toJson id)

private def templateScope : ScopeTemplate → Lean.Json
  | .any => obj [("op", Lean.toJson "All")]
  | .eq value => obj [("op", Lean.toJson "=="), entityOrSlot value]
  | .mem value => obj [("op", Lean.toJson "in"), entityOrSlot value]
  | .is ty => obj [("op", Lean.toJson "is"),
      ("entity_type", Lean.toJson (toString ty))]
  | .isMem ty value => obj [("op", Lean.toJson "is"),
      ("entity_type", Lean.toJson (toString ty)),
      ("in", obj [entityOrSlot value])]

/-- Serialize a Cedar template while retaining its unbound slots. -/
def template (id : TemplateID) (value : Template) : Except Error Lean.Json := do
  let .principalScope principal := value.principalScope
  let .resourceScope resource := value.resourceScope
  return obj [
    ("effect", Lean.toJson (match value.effect with
      | .permit => "permit"
      | .forbid => "forbid")),
    ("principal", templateScope principal),
    ("action", ← actionScope id value.actionScope),
    ("resource", templateScope resource),
    ("conditions", Lean.toJson (← value.condition.mapM (condition id)))]

/-- Export static policies, active editable templates, and links in one Cedar
    JSON policy set. The caller separately certifies the linked result. -/
def sourceSet (staticPolicies : Policies) (templates : Templates)
    (links : TemplateLinkedPolicies) :
    Except Error Lean.Json := do
  let static ← staticEntries staticPolicies
  let templateEntries := Cedar.Data.Map.toList templates
  if !(decide (templateEntries.map Prod.fst).Nodup) then
    throw .duplicateTemplateId
  if !(decide (links.map TemplateLinkedPolicy.id).Nodup) then
    throw .duplicateTemplateLinkId
  for (id, _) in templateEntries do
    if !(links.any fun link => link.templateId == id) then
      throw (.unlinkedTemplateId id)
  for link in links do
    if static.any (fun entry => entry.1 == link.id) then
      throw (.duplicatePolicyId link.id)
  let _ ← (Cedar.Spec.link? templates links).mapError .invalidTemplateLink
  let exportedTemplates ← templateEntries.mapM fun (id, value) => do
    return (id, ← template id value)
  let exportedLinks ← links.mapM fun link => do
    let slots := Cedar.Data.Map.toList link.slotEnv
    if !(decide (slots.map Prod.fst).Nodup) then
      throw .duplicateSlotBinding
    return obj [("newId", Lean.toJson link.id),
      ("templateId", Lean.toJson link.templateId),
      ("values", obj (slots.map fun (id, uid) => (id, entity uid)))]
  return obj [("staticPolicies", obj static),
    ("templates", obj exportedTemplates),
    ("templateLinks", Lean.toJson exportedLinks)]

/-- Export an entirely template-linked source set. -/
def templateSet (templates : Templates) (links : TemplateLinkedPolicies) :
    Except Error Lean.Json :=
  sourceSet [] templates links

private def valueFuel : Nat → Value → Except Error Lean.Json
  | 0, _ => .error .valueDepthExceeded
  | _fuel + 1, .prim (.bool b) => .ok (Lean.toJson b)
  | _fuel + 1, .prim (.int n) => .ok (Lean.toJson n.toInt)
  | _fuel + 1, .prim (.string s) => .ok (Lean.toJson s)
  | _fuel + 1, .prim (.entityUID uid) => .ok (obj [("__entity", entity uid)])
  | fuel + 1, .set members => do
      return Lean.toJson (← members.toList.mapM (valueFuel fuel))
  | fuel + 1, .record attrs => do
      if !(uniqueRecordKeys attrs.toList) then
        throw .duplicateEntityAttribute
      let fields ← attrs.toList.mapM fun (key, val) => do
        return (key, ← valueFuel fuel val)
      return obj fields
  | _fuel + 1, .ext (.decimal amount) =>
      .ok (obj [("__extn", obj [("fn", Lean.toJson "decimal"),
        ("arg", Lean.toJson (toString amount))])])
  | _fuel + 1, .ext (.ipaddr address) =>
      .ok (obj [("__extn", obj [("fn", Lean.toJson "ip"),
        ("arg", Lean.toJson (toString address))])])
  | _fuel + 1, .ext (.datetime timestamp) =>
      let millis := Std.Time.Millisecond.Offset.ofInt timestamp.val.toInt
      let utc := Std.Time.DateTime.ofTimestampWithZone
        (Std.Time.Timestamp.ofMillisecondsSinceUnixEpoch millis) Std.Time.TimeZone.UTC
      let format : Std.Time.GenericFormat .any :=
        Std.Time.GenericFormat.spec! "yyyy-MM-dd'T'HH:mm:ss.SSS'Z'"
      let encoded := format.format utc
      if Cedar.Spec.Ext.Datetime.parse encoded == some timestamp then
        .ok (obj [("__extn", obj [("fn", Lean.toJson "datetime"),
          ("arg", Lean.toJson encoded)])])
      else .error .unsupportedValue
  | _fuel + 1, .ext (.duration duration) =>
      let encoded := s!"{duration.val.toInt}ms"
      if Cedar.Spec.Ext.Datetime.Duration.parse encoded == some duration then
        .ok (obj [("__extn", obj [("fn", Lean.toJson "duration"),
          ("arg", Lean.toJson encoded)])])
      else .error .unsupportedValue

private def value (input : Value) : Except Error Lean.Json :=
  valueFuel 1024 input

private def attrs (values : Cedar.Data.Map String Value) : Except Error Lean.Json := do
  if !(uniqueRecordKeys values.toList) then
    throw .duplicateEntityAttribute
  let fields ← values.toList.mapM fun (key, val) => do
    return (key, ← value val)
  return obj fields

/-- Export Cedar entities using the public entity JSON format. -/
def entities (values : Cedar.Spec.Entities) : Except Error Lean.Json := do
  let rows ← Cedar.Data.Map.toList values |>.mapM fun (uid, data) => do
    if data.ancestors.contains uid then
      throw (.incompleteEntityAncestors uid)
    for ancestor in data.ancestors.toList do
      if let some ancestorData := values.find? ancestor then
        if !ancestorData.ancestors.subset data.ancestors then
          throw (.incompleteEntityAncestors uid)
    return obj [
      ("uid", entity uid),
      ("attrs", ← attrs data.attrs),
      ("parents", Lean.toJson (data.ancestors.toList.map entity)),
      ("tags", ← attrs data.tags)]
  return Lean.toJson rows

/-- Export a request with explicit Cedar entity UIDs and context. -/
def request (req : Cedar.Spec.Request) : Except Error Lean.Json := do
  return obj [
    ("principal", Lean.toJson (toString req.principal)),
    ("action", Lean.toJson (toString req.action)),
    ("resource", Lean.toJson (toString req.resource)),
    ("context", ← attrs req.context)]

/-- Compile POO edits, then export the resulting ordinary Cedar policies. -/
def compiled (model : PolicyModules.Model) (root : String) :
    Except (Sum PolicyModules.Error Error) Lean.Json := do
  let policies ← (model.compile root).mapError Sum.inl
  (policySet policies).mapError Sum.inr

inductive PublicationError where
  | composition (error : PolicyModules.Error)
  | schema (error : Cedar.Validation.EnvironmentValidationError)
  | policy (error : Cedar.Validation.ValidationError)
  | export (error : Error)
  | duplicatePolicyIds

/-- A publication carries the exact compiled set and Cedar validation premises. -/
structure Publication (model : PolicyModules.Model) (root : String)
    (schema : Cedar.Validation.Schema) extends PolicyPreparation.Validated model root schema where
  idsUnique : (policies.map Policy.id).Nodup
  json : Lean.Json
  serialized : policySet policies = .ok json
  snapshot : Transport.SourceSnapshot .policy
  snapshot_value : snapshot.value = json
  /-- Immutable policy metadata belongs to the checked publication, not each request. -/
  identifiers : Thunk { value : Lean.Json // value = Lean.toJson (policies.map Policy.id) } :=
    Thunk.mk fun _ => ⟨Lean.toJson (policies.map Policy.id), rfl⟩

private theorem policyIdsUniqueOfNodup (policies : Policies)
    (unique : (policies.map Policy.id).Nodup) :
    Cedar.Thm.PolicyIdsUnique policies := by
  induction policies with
  | nil => simp [Cedar.Thm.PolicyIdsUnique]
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at unique
      grind [Cedar.Thm.PolicyIdsUnique]

/-- Publication discharges Cedar's unique-ID premise for response soundness. -/
theorem Publication.policyIdsUnique (publication : Publication model root schema) :
    Cedar.Thm.PolicyIdsUnique publication.policies :=
  policyIdsUniqueOfNodup publication.policies publication.idsUnique

/-- Produce a Lean-validated artifact. The Rust consumer must still admit the
    JSON through Cedar's official policy-set parser before deployment. -/
def publishValidated (checked : PolicyPreparation.Validated model root schema) :
    Except PublicationError (Publication model root schema) :=
  match hj : policySet checked.policies with
  | .error error => .error (.export error)
  | .ok json =>
      if unique : (checked.policies.map Policy.id).Nodup then
        .ok {
          toValidated := checked
          idsUnique := unique
          json
          serialized := hj
          snapshot := Transport.SourceSnapshot.ofJson json
          snapshot_value := rfl }
      else .error .duplicatePolicyIds

def publish (model : PolicyModules.Model) (root : String)
    (schema : Cedar.Validation.Schema) :
    Except PublicationError (Publication model root schema) := do
  let compiled ← (PolicyPreparation.compile model root).mapError .composition
  let checked ← PolicyPreparation.check compiled schema PublicationError.schema PublicationError.policy
  publishValidated checked

/-- Render exact serialized policies and an actual Cedar response. Witnesses
bind both inputs; shared consumers need no second compilation or authorization. -/
def authorizationCaseData (name revision : String) (policies : Policies)
    (exported : Lean.Json) (req : Request) (store : Entities) (response : Response)
    (_serialized : policySet policies = .ok exported)
    (_evaluated : response = isAuthorized req store policies) : Except String Lean.Json := do
  let convert {α β : Type} [Repr α] (result : Except α β) : Except String β :=
    result.mapError reprStr
  let exportedEntities ← convert (entities store)
  let exportedRequest ← convert (request req)
  return obj [
    ("name", Lean.toJson name),
    ("revision", Lean.toJson revision),
    ("policy_ids", Lean.toJson (policies.map Policy.id)),
    ("policies", exported),
    ("entities", exportedEntities),
    ("request", exportedRequest),
    ("expected", Lean.toJson (match response.decision with
      | .allow => "allow"
      | .deny => "deny")),
    ("expected_reasons", Lean.toJson response.determiningPolicies.toList),
    ("expected_error_policies", Lean.toJson response.erroringPolicies.toList)]


/-- Render the exact typed compilation without adding a schema premise. -/
def authorizationCaseCompiled (compiled : PolicyPreparation.Compiled model root)
    (name revision : String) (req : Request) (store : Entities) : Except String Lean.Json := do
  match h : policySet compiled.policies with
  | .error error => .error (reprStr error)
  | .ok exported =>
      authorizationCaseData name revision compiled.policies exported req store
        (isAuthorized req store compiled.policies) h rfl

/-- Compile-only compatibility entrypoint retains its exact error order. -/
def authorizationCase (name revision : String) (model : PolicyModules.Model)
    (root : String) (req : Request) (store : Entities) : Except String Lean.Json := do
  let compiled ← (PolicyPreparation.compile model root).mapError reprStr
  authorizationCaseCompiled compiled name revision req store

end CedarPooSpec.PolicyJson
