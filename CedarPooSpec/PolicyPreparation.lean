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

def compile (model : Model) (root : String) : Except PolicyModules.Error (Compiled model root) :=
  match h : model.compile root with
  | .error error => .error error
  | .ok policies => .ok ⟨policies, h⟩

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

end CedarPooSpec.PolicyPreparation
