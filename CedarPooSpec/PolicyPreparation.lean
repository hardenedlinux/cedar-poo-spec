import CedarPooSpec.PolicyModules
import CedarPooSpec.SchemaAdmission

/-! Exact compiled and validated Cedar values, shared by publication and
Functional consumers. Each witness belongs to the actual model/root/schema. -/
namespace CedarPooSpec.PolicyPreparation

open Cedar.Spec Cedar.Validation CedarPooSpec.PolicyModules

structure Compiled (model : Model) (root : String) where
  policies : Policies
  compiled : model.compile root = .ok policies

structure Validated (model : Model) (root : String) (schema : Schema)
    extends Compiled model root where
  schemaDefinitionsValid : SchemaAdmission.validateDefinitions schema = .ok ()
  schemaValid : schema.validateWellFormed = .ok ()
  policyValid : validate policies schema = .ok ()

/-- Pure schema facts, bound to their full immutable source and forced only
after compilation succeeds. Sharing never retains policy admission. -/
structure SchemaFacts (schema : Schema) where
  definitions : Thunk { result : Except EnvironmentValidationError Unit //
    result = SchemaAdmission.validateDefinitions schema }
  wellFormed : Thunk { result : Except EnvironmentValidationError Unit //
    result = schema.validateWellFormed }

def SchemaFacts.prepare (schema : Schema) : SchemaFacts schema :=
  ⟨Thunk.mk fun _ => ⟨SchemaAdmission.validateDefinitions schema, rfl⟩,
   Thunk.mk fun _ => ⟨schema.validateWellFormed, rfl⟩⟩

def compile (model : Model) (root : String) : Except PolicyModules.Error (Compiled model root) :=
  match h : model.compile root with
  | .error error => .error error
  | .ok policies => .ok ⟨policies, h⟩

def compilePrepared (model : Model) (prepared : LeanPoo.C4.Prepared model.graph)
    (root : String) : Except PolicyModules.Error (Compiled model root) :=
  match h : model.compilePrepared prepared root with
  | .error error => .error error
  | .ok policies => .ok ⟨policies, by simpa only [model.compilePrepared_eq] using h⟩

theorem compilePrepared_eq (model : Model) (prepared : LeanPoo.C4.Prepared model.graph)
    (root : String) : compilePrepared model prepared root = compile model root := by
  have same := model.compilePrepared_eq prepared root
  unfold compilePrepared compile
  split <;> split <;> simp_all

theorem compile_error (h : model.compile root = .error error) :
    compile model root = .error error := by
  unfold compile
  split
  next other eq =>
    have same := Except.error.inj (eq.symm.trans h)
    subst other
    rfl
  next _ eq => have impossible := eq.symm.trans h; contradiction

theorem compile_ok (h : model.compile root = .ok policies) :
    compile model root = .ok ⟨policies, h⟩ := by
  unfold compile
  split
  next _ eq => have impossible := eq.symm.trans h; contradiction
  next other eq =>
    have same := Except.ok.inj (eq.symm.trans h)
    subst other
    rfl

/-- Preserve the original definition/well-formedness/policy error order.
The callbacks only lift original Cedar errors into a consumer's error sum. -/
def check {Error : Type} (compiled : Compiled model root) (schema : Schema)
    (schemaError : EnvironmentValidationError → Error)
    (policyError : ValidationError → Error) : Except Error (Validated model root schema) :=
  match ha : SchemaAdmission.validateDefinitions schema with
  | .error error => .error (schemaError error)
  | .ok () =>
    match hs : schema.validateWellFormed with
    | .error error => .error (schemaError error)
    | .ok () =>
      match hv : validate compiled.policies schema with
      | .error error => .error (policyError error)
      | .ok () => .ok {
          toCompiled := compiled
          schemaDefinitionsValid := ha
          schemaValid := hs
          policyValid := hv }

theorem check_definitions_error {Error : Type} (compiled : Compiled model root)
    (se : EnvironmentValidationError → Error) (pe : ValidationError → Error)
    (h : SchemaAdmission.validateDefinitions schema = .error error) :
    check compiled schema se pe = .error (se error) := by
  unfold check
  split
  next other eq =>
    have same := Except.error.inj (eq.symm.trans h)
    subst other
    rfl
  next eq => have impossible := eq.symm.trans h; contradiction

theorem check_schema_error {Error : Type} (compiled : Compiled model root)
    (se : EnvironmentValidationError → Error) (pe : ValidationError → Error)
    (ha : SchemaAdmission.validateDefinitions schema = .ok ())
    (h : schema.validateWellFormed = .error error) :
    check compiled schema se pe = .error (se error) := by
  unfold check
  split
  next _ eq => have impossible := eq.symm.trans ha; contradiction
  next _ =>
    split
    next other eq =>
      have same := Except.error.inj (eq.symm.trans h)
      subst other
      rfl
    next eq => have impossible := eq.symm.trans h; contradiction

theorem check_policy_error {Error : Type} (compiled : Compiled model root)
    (se : EnvironmentValidationError → Error) (pe : ValidationError → Error)
    (ha : SchemaAdmission.validateDefinitions schema = .ok ())
    (hs : schema.validateWellFormed = .ok ())
    (h : validate compiled.policies schema = .error error) :
    check compiled schema se pe = .error (pe error) := by
  unfold check
  split
  next _ eq => have impossible := eq.symm.trans ha; contradiction
  next _ =>
    split
    next _ eq => have impossible := eq.symm.trans hs; contradiction
    next _ =>
      split
      next other eq =>
        have same := Except.error.inj (eq.symm.trans h)
        subst other
        rfl
      next eq => have impossible := eq.symm.trans h; contradiction

theorem check_ok {Error : Type} (compiled : Compiled model root)
    (se : EnvironmentValidationError → Error) (pe : ValidationError → Error)
    (ha : SchemaAdmission.validateDefinitions schema = .ok ())
    (hs : schema.validateWellFormed = .ok ())
    (hv : validate compiled.policies schema = .ok ()) :
    check compiled schema se pe = .ok {
      toCompiled := compiled, schemaDefinitionsValid := ha, schemaValid := hs, policyValid := hv } := by
  unfold check
  split
  next _ eq => have impossible := eq.symm.trans ha; contradiction
  next _ =>
    split
    next _ eq => have impossible := eq.symm.trans hs; contradiction
    next _ =>
      split
      next _ eq => have impossible := eq.symm.trans hv; contradiction
      next _ => rfl

/-- Same per-policy validation and error order, using exact shared schema facts. -/
def checkUsing {Error : Type} (compiled : Compiled model root)
    (facts : SchemaFacts schema)
    (schemaError : EnvironmentValidationError → Error)
    (policyError : ValidationError → Error) : Except Error (Validated model root schema) :=
  match ha : facts.definitions.get.val with
  | .error error => .error (schemaError error)
  | .ok () =>
    match hs : facts.wellFormed.get.val with
    | .error error => .error (schemaError error)
    | .ok () =>
      match hv : validate compiled.policies schema with
      | .error error => .error (policyError error)
      | .ok () => .ok {
          toCompiled := compiled
          schemaDefinitionsValid := facts.definitions.get.property.symm.trans ha
          schemaValid := facts.wellFormed.get.property.symm.trans hs
          policyValid := hv }

theorem checkUsing_eq {Error : Type} (compiled : Compiled model root)
    (facts : SchemaFacts schema) (se : EnvironmentValidationError → Error)
    (pe : ValidationError → Error) :
    checkUsing compiled facts se pe = check compiled schema se pe := by
  unfold checkUsing
  split
  next error hd =>
    exact (check_definitions_error compiled se pe
      (facts.definitions.get.property.symm.trans hd)).symm
  next hd =>
    have originalD := facts.definitions.get.property.symm.trans hd
    split
    next error hw =>
      exact (check_schema_error compiled se pe originalD
        (facts.wellFormed.get.property.symm.trans hw)).symm
    next hw =>
      have originalW := facts.wellFormed.get.property.symm.trans hw
      split
      next error hv => exact (check_policy_error compiled se pe originalD originalW hv).symm
      next hv => exact (check_ok compiled se pe originalD originalW hv).symm

end CedarPooSpec.PolicyPreparation
