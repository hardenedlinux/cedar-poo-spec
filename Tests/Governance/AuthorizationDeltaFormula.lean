import CedarPooSpec.Authorization.Delta.OperationalExactProof
import CedarPooSpec.Authorization.Delta.BooleanCore
import Examples.Governance.TicketSharing

open Cedar.Spec Cedar.Validation Cedar.SymCC
open CedarPooSpec.Authorization.Delta
open CedarPooSpec.TicketSharingExample

namespace CedarPooSpec.AuthorizationDeltaFixture

def typeEnv : TypeEnv := schema.environments.head!
def symEnv : SymEnv := SymEnv.ofTypeEnv typeEnv
def before := (wellTypedPolicies publishedPolicies typeEnv).toOption.get (by native_decide)
def after := (wellTypedPolicies posturePolicies typeEnv).toOption.get (by native_decide)
def asserts := (verifyErrorFreeAllowExpansion before after symEnv).toOption.get (by native_decide)

def attrs : UnaryFunction := (symEnv.entities.attrs ticketType).get (by decide)
def pb : Term := Factory.eq symEnv.request.principal (.entity bob)
def pa : Term := Factory.eq symEnv.request.principal (.entity alice)
def ra : Term := Factory.eq symEnv.request.resource (.entity ticketA)
def rb : Term := Factory.eq symEnv.request.resource (.entity ticketB)
def st : Term := Factory.eq (Factory.record.get (Factory.app attrs symEnv.request.resource) "status") (.string "OPEN")
def td : Term := Factory.record.get symEnv.request.context "deviceTrusted"
def base : Term := Factory.and pb (Factory.and ra st)
def v2b : Term := Factory.and pb (Factory.and rb (Factory.and st td))
def v2a : Term := Factory.and pa (Factory.and ra (Factory.and st td))
def v1b : Term := Factory.and pb (Factory.and rb st)
def v1a : Term := Factory.and pa (Factory.and ra st)
def formula : Term := Factory.and (Factory.or base (Factory.or v2b v2a))
  (Factory.not (Factory.or base (Factory.or v1b v1a)))

private def concreteTypeEnv : TypeEnv :=
  ⟨schema.ets, schema.acts, ⟨userType, readAction, ticketType, contextType⟩⟩

private theorem principalType : symEnv.request.principal.typeOf = .entity userType := by
  change (SymEnv.ofTypeEnv concreteTypeEnv).request.principal.typeOf = _
  simp [SymEnv.ofTypeEnv, SymEnv.ofEnv, SymRequest.ofRequestType,
    TermType.ofType, concreteTypeEnv]

private theorem resourceType : symEnv.request.resource.typeOf = .entity ticketType := by
  change (SymEnv.ofTypeEnv concreteTypeEnv).request.resource.typeOf = _
  simp [SymEnv.ofTypeEnv, SymEnv.ofEnv, SymRequest.ofRequestType,
    TermType.ofType, concreteTypeEnv]

private theorem contextTermType :
    symEnv.request.context.typeOf =
      .record (Cedar.Data.Map.mk [("deviceTrusted", TermType.bool)]) := by
  change (SymEnv.ofTypeEnv concreteTypeEnv).request.context.typeOf = _
  simp [SymEnv.ofTypeEnv, SymEnv.ofEnv, SymRequest.ofRequestType,
    TermType.ofType, concreteTypeEnv, contextType]
  decide

/-- The pinned, typechecked ticket-sharing revision generates exactly this
    two-assertion symbolic query. This is a structural identity, not an UNSAT proof. -/
theorem exactQueryShape : asserts = [(true : Term), formula] := by
  native_decide

/-- The concrete ticket-sharing symbols are well-formed for the pinned schema. -/
private theorem principalWF : symEnv.request.principal.WellFormed symEnv.entities := by
  apply Term.WellFormed.var_wf
  apply TermType.WellFormed.entity_wf
  decide

private theorem resourceWF : symEnv.request.resource.WellFormed symEnv.entities := by
  apply Term.WellFormed.var_wf
  apply TermType.WellFormed.entity_wf
  decide

private theorem bobWF : (Term.prim (.entity bob)).WellFormed symEnv.entities := by
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.entity_wf
  decide

private theorem aliceWF : (Term.prim (.entity alice)).WellFormed symEnv.entities := by
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.entity_wf
  decide

private theorem ticketAWF : (Term.prim (.entity ticketA)).WellFormed symEnv.entities := by
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.entity_wf
  decide

private theorem ticketBWF : (Term.prim (.entity ticketB)).WellFormed symEnv.entities := by
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.entity_wf
  decide

private theorem contextWF : symEnv.request.context.WellFormed symEnv.entities := by
  apply Term.WellFormed.var_wf
  apply TermType.WellFormed.record_wf
  · intro a ty h
    change (Cedar.Data.Map.mk [("deviceTrusted", TermType.bool)]).find? a = some ty at h
    by_cases ha : a = "deviceTrusted"
    · subst a
      simp [Cedar.Data.Map.find?] at h
      subst ty
      exact TermType.WellFormed.bool_wf
    · simp [Cedar.Data.Map.find?, Ne.symm ha] at h
  · change (Cedar.Data.Map.mk [("deviceTrusted", TermType.bool)]).WellFormed
    rfl

private theorem attrsWF : attrs.WellFormed symEnv.entities := by
  change (TermType.entity ticketType).WellFormed symEnv.entities ∧
    (TermType.record (Cedar.Data.Map.mk [("status", TermType.string)])).WellFormed symEnv.entities
  constructor
  · apply TermType.WellFormed.entity_wf
    decide
  · apply TermType.WellFormed.record_wf
    · intro a ty h
      change (Cedar.Data.Map.mk [("status", TermType.string)]).find? a = some ty at h
      by_cases ha : a = "status"
      · subst a
        simp [Cedar.Data.Map.find?] at h
        subst ty
        exact TermType.WellFormed.string_wf
      · simp [Cedar.Data.Map.find?, Ne.symm ha] at h
    · rfl

private theorem pbWF : pb.WellFormed symEnv.entities ∧ pb.typeOf = .bool := by
  exact Cedar.Thm.wf_eq principalWF bobWF (by simpa [bob] using principalType)

private theorem paWF : pa.WellFormed symEnv.entities ∧ pa.typeOf = .bool := by
  exact Cedar.Thm.wf_eq principalWF aliceWF (by simpa [alice] using principalType)

private theorem raWF : ra.WellFormed symEnv.entities ∧ ra.typeOf = .bool := by
  exact Cedar.Thm.wf_eq resourceWF ticketAWF (by simpa [ticketA] using resourceType)

private theorem rbWF : rb.WellFormed symEnv.entities ∧ rb.typeOf = .bool := by
  exact Cedar.Thm.wf_eq resourceWF ticketBWF (by simpa [ticketB] using resourceType)

private theorem stWF : st.WellFormed symEnv.entities ∧ st.typeOf = .bool := by
  have hArg : symEnv.request.resource.typeOf = attrs.argType := by
    rw [resourceType]
    change TermType.entity ticketType = TermType.entity ticketType
    rfl
  have happ := Cedar.Thm.wf_app resourceWF hArg attrsWF
  have hget := Cedar.Thm.wf_record_get happ.1
    (by
      calc
        (Factory.app attrs symEnv.request.resource).typeOf = attrs.outType := happ.2
        _ = TermType.record (Cedar.Data.Map.mk [("status", TermType.string)]) := by rfl)
    (by decide : (Cedar.Data.Map.mk [("status", TermType.string)]).find? "status" = some TermType.string)
  have hstr : (Term.prim (.string "OPEN")).WellFormed symEnv.entities := Cedar.Thm.wf_string
  exact Cedar.Thm.wf_eq hget.1 hstr (by
    calc
      (Factory.record.get (Factory.app attrs symEnv.request.resource) "status").typeOf =
          TermType.string := hget.2
      _ = (Term.string "OPEN").typeOf :=
        Cedar.Thm.typeOf_term_prim_string.symm)

private theorem tdWF : td.WellFormed symEnv.entities ∧ td.typeOf = .bool := by
  exact Cedar.Thm.wf_record_get contextWF
    (by simpa only using contextTermType : symEnv.request.context.typeOf =
      TermType.record (Cedar.Data.Map.mk [("deviceTrusted", TermType.bool)]))
    (by decide : (Cedar.Data.Map.mk [("deviceTrusted", TermType.bool)]).find? "deviceTrusted" = some TermType.bool)

/-- UNSAT for the pinned ticket-sharing query. The six atom well-formedness
    proofs and reusable Boolean implication are kernel checked. Construction
    of the compiled revision and exact query shape still uses `native_decide`. -/
theorem exactUnsat : symEnv ⊭ asserts :=
  CedarPooSpec.Authorization.Delta.BooleanCore.unsatOfShapeAndWellFormedAtoms
    symEnv asserts pb pa ra rb st td
    (by simpa only [formula, base, v2b, v2a, v1b, v1a,
      CedarPooSpec.Authorization.Delta.BooleanCore.formula] using exactQueryShape)
    pbWF paWF raWF rbWF stWF tdWF

theorem singletonTypeEnvironment : schema.environments = [typeEnv] := by
  rfl

theorem schemaWF : schema.validateWellFormed = .ok () := by
  have hOk : schema.validateWellFormed.isOk = true := by native_decide
  cases h : schema.validateWellFormed with
  | ok u => cases u; rfl
  | error e => simp [h, Except.isOk, Except.toBool] at hOk

theorem typecheckedBefore : wellTypedPolicies publishedPolicies typeEnv = .ok before := by
  have hOk : (wellTypedPolicies publishedPolicies typeEnv).isOk = true := by native_decide
  cases h : wellTypedPolicies publishedPolicies typeEnv with
  | ok ps => simp only [before, h, Except.toOption] ; rfl
  | error e => simp [h, Except.isOk, Except.toBool] at hOk

theorem typecheckedAfter : wellTypedPolicies posturePolicies typeEnv = .ok after := by
  have hOk : (wellTypedPolicies posturePolicies typeEnv).isOk = true := by native_decide
  cases h : wellTypedPolicies posturePolicies typeEnv with
  | ok ps => simp only [after, h, Except.toOption] ; rfl
  | error e => simp [h, Except.isOk, Except.toBool] at hOk

theorem exactQuery : verifyErrorFreeAllowExpansion before after symEnv = .ok asserts := by
  have hOk : (verifyErrorFreeAllowExpansion before after symEnv).isOk = true := by native_decide
  cases h : verifyErrorFreeAllowExpansion before after symEnv with
  | ok xs => simp only [asserts, h, Except.toOption] ; rfl
  | error e => simp [h, Except.isOk, Except.toBool] at hOk

/-- For validated, strongly well-formed ticket-sharing requests and policy
    references, these exact linked Cedar policy lists cannot gain an error-free
    Allow. This theorem does not depend on the C4 model construction. -/
theorem noGainForValidatedPolicyBodies
    (env : Cedar.Spec.Env)
    (hRequest : Cedar.Validation.validateRequest schema env.request = .ok ())
    (hEntities : Cedar.Validation.validateEntities schema env.entities = .ok ())
    (hEnv : env.StronglyWellFormed)
    (hBefore : env.StronglyWellFormedForPolicies publishedPolicies)
    (hAfter : env.StronglyWellFormedForPolicies posturePolicies)
    (hAllowed : errorFreeAllow posturePolicies env = true) :
    errorFreeAllow publishedPolicies env = true := by
  apply noErrorFreeAllowExpansionForValidatedSchema schema
    publishedPolicies posturePolicies schemaWF
    (by
      intro Γ hΓ
      rw [singletonTypeEnvironment] at hΓ
      simp only [List.mem_singleton] at hΓ
      subst Γ
      exact ⟨before, after, asserts, typecheckedBefore, typecheckedAfter,
        exactQuery, exactUnsat⟩)
    env hRequest hEntities hEnv hBefore hAfter hAllowed

/-- The compiled Published-to-Posture C4 revision has the linked policy bodies
    above. This is the separate model-to-policy bridge. -/
theorem noGainForValidatedTicketSharing
    (env : Cedar.Spec.Env)
    (hRequest : Cedar.Validation.validateRequest schema env.request = .ok ())
    (hEntities : Cedar.Validation.validateEntities schema env.entities = .ok ())
    (hEnv : env.StronglyWellFormed)
    (hBefore : env.StronglyWellFormedForPolicies policyRevision.beforePolicies)
    (hAfter : env.StronglyWellFormedForPolicies policyRevision.afterPolicies)
    (hAllowed : errorFreeAllow policyRevision.afterPolicies env = true) :
    errorFreeAllow policyRevision.beforePolicies env = true := by
  obtain ⟨hBeforeBodies, hAfterBodies⟩ := policyRevisionBodies
  rw [hBeforeBodies] at hBefore ⊢
  rw [hAfterBodies] at hAfter hAllowed
  exact noGainForValidatedPolicyBodies env hRequest hEntities hEnv hBefore hAfter hAllowed


end CedarPooSpec.AuthorizationDeltaFixture
