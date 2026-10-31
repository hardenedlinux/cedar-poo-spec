import CedarPooSpec.Authorization.Delta.Release
import CedarPooSpec.ZeroTrust
import LeanPoo.Functional.EvidenceBinding

/-! Application adapter joining an existing LeanPoo invocation, the generic
Zero Trust requirements and the Host's final publication transition. No ledger
or publication IO is implemented. The Host must provide authenticated reference
meanings and serialize all guards with the actual commit. -/
namespace CedarPooSpec.Gateway.PublicationReview
open LeanPoo.Functional.DeclarativeMetadata

/-- An authority-issued binding, not a source-role token or caller-supplied
labels. Cryptographic verification and custody remain adapter obligations. -/
structure RegistrarBinding (Subject Incarnation PublicKey Scope Audience : Type) where
  subject : Subject
  incarnation : Incarnation
  publicKey : PublicKey
  scope : Scope
  audience : Audience
  epoch : Nat
  serial : Nat
  deriving DecidableEq

structure RegistrarAuthority (Command View Subject Incarnation PublicKey Scope Audience : Type) where
  current : View → RegistrarBinding Subject Incarnation PublicKey Scope Audience
  issued : RegistrarBinding Subject Incarnation PublicKey Scope Audience → View → Prop
  roleAllowed : Subject → View → Prop
  expectedScope : View → Scope
  expectedAudience : View → Audience
  revoked : RegistrarBinding Subject Incarnation PublicKey Scope Audience → View → Prop
  possession : RegistrarBinding Subject Incarnation PublicKey Scope Audience → Command → View → Prop

def RegistrarAuthority.admitted
    (authority : RegistrarAuthority Command View Subject Incarnation PublicKey Scope Audience)
    (binding : RegistrarBinding Subject Incarnation PublicKey Scope Audience)
    (command : Command) (view : View) : Prop :=
  authority.issued binding view ∧ authority.roleAllowed binding.subject view ∧
    binding = authority.current view ∧ binding.scope = authority.expectedScope view ∧
    binding.audience = authority.expectedAudience view ∧ ¬ authority.revoked binding view ∧
    authority.possession binding command view

theorem registrar_admission_retains_exact_binding
    {authority : RegistrarAuthority Command View Subject Incarnation PublicKey Scope Audience}
    {binding command view} (accepted : authority.admitted binding command view) :
    binding = authority.current view ∧ ¬ authority.revoked binding view ∧
      authority.possession binding command view :=
  ⟨accepted.2.2.1, accepted.2.2.2.2.2.1, accepted.2.2.2.2.2.2⟩

theorem substituted_registrar_binding_is_refused
    {authority : RegistrarAuthority Command View Subject Incarnation PublicKey Scope Audience}
    {binding command view} (different : binding ≠ authority.current view) :
    ¬ authority.admitted binding command view := fun accepted => different accepted.2.2.1

theorem revoked_registrar_binding_is_refused
    {authority : RegistrarAuthority Command View Subject Incarnation PublicKey Scope Audience}
    {binding command view} (revoked : authority.revoked binding view) :
    ¬ authority.admitted binding command view := fun accepted => accepted.2.2.2.2.2.1 revoked

theorem unbound_registrar_command_is_refused
    {authority : RegistrarAuthority Command View Subject Incarnation PublicKey Scope Audience}
    {binding command view} (missing : ¬ authority.possession binding command view) :
    ¬ authority.admitted binding command view := fun accepted => missing accepted.2.2.2.2.2.2

structure Host (Command Result View Parent Artifact Cut : Type) where
  security : ZeroTrust.Framework Command View
  parentAt : View → Parent
  approvedEvidenceAt : View → Command → Option Artifact
  registrationCommitted : View → Command → Artifact → Prop
  registryRecovered : View → Prop
  registrarCurrent : Command → View → Prop
  cutAt : View → Cut
  projection : Result → Command × (Parent × Option Artifact) × Cut
  /-- Command-specific admission may resolve its own staged intent and leave
  siblings pending. This is not the provider effect's global pending barrier. -/
  pendingAdmissible : Command → View → Prop
  commit : View → Result → View → Prop

variable {Command Result View Parent Artifact Cut Atom Error : Type}
  [DecidableEq Command] [DecidableEq Parent] [DecidableEq Artifact] [DecidableEq Cut]

/-- Expected references come from the independent authority's actual deciding
view. A candidate cannot choose another parent or evidence to satisfy this
Contract. Reference equality alone does not authenticate any of these readers. -/
def Host.contract (host : Host Command Result View Parent Artifact Cut)
    (template : Contract Atom Command Result) (command : Command) (actual : View) :=
  template.bindEvidence command
    (host.parentAt actual, host.approvedEvidenceAt actual command)
    (host.cutAt actual) host.projection

/-- A commit witness, not a transport or affine execution capability. Prepare
is pure and captures the actual pre-state; invoking it may perform no external
send. Native atomicity and trusted readers are explicit Host obligations. -/
structure Final (host : Host Command Result View Parent Artifact Cut)
    (template : Contract Atom Command Result)
    (prepare : View → Command → Except Error (Result × View))
    (command : Command) (actual : View) where
  receipt : Invocation (host.contract template command actual) (prepare actual) command
  approved : ∃ artifact, host.approvedEvidenceAt actual command = some artifact
  durable : ∀ artifact, host.approvedEvidenceAt actual command = some artifact →
    host.registrationCommitted actual command artifact
  recovered : host.registryRecovered actual
  fenced : host.registrarCurrent command actual
  current : host.security.required command actual
  pending : host.pendingAdmissible command actual
  committed : host.commit actual receipt.result receipt.state

variable {prepare : View → Command → Except Error (Result × View)}

theorem final_preserves_original_and_binding
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (publication : Final host template prepare command actual) :
    template.rule.Holds (fun atom => template.meaning atom command publication.receipt.result) ∧
      host.projection publication.receipt.result =
        (command, (host.parentAt actual, host.approvedEvidenceAt actual command), host.cutAt actual) := by
  have bound := template.bindEvidence_accepted command
    (host.parentAt actual, host.approvedEvidenceAt actual command)
    (host.cutAt actual) host.projection (prepare actual) command publication.receipt
  exact ⟨bound.1, bound.2.2⟩

theorem final_retains_continuous_authorization
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (publication : Final host template prepare command actual) :
    host.security.currentAtUse actual ∧ host.security.authorized command actual ∧
      host.security.consumptionCommitted command actual ∧
      host.security.unknownRetained command actual ∧ host.pendingAdmissible command actual :=
  ⟨publication.current.2.2.1, publication.current.2.1,
    publication.current.2.2.2.1, publication.current.2.2.2.2.1, publication.pending⟩

theorem changed_binding_cannot_commit
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (changed : ∀ result, prepare actual command = .ok result →
      host.projection result.1 ≠
        (command, (host.parentAt actual, host.approvedEvidenceAt actual command), host.cutAt actual)) :
    ¬ Nonempty (Final host template prepare command actual) := by
  rintro ⟨publication⟩
  exact changed _ publication.receipt.called
    (final_preserves_original_and_binding publication).2

theorem unqualified_pending_cannot_commit
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (pending : ¬ host.pendingAdmissible command actual) :
    ¬ Nonempty (Final host template prepare command actual) :=
  fun ⟨publication⟩ => pending publication.pending

theorem missing_review_cannot_commit
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (missing : host.approvedEvidenceAt actual command = none) :
    ¬ Nonempty (Final host template prepare command actual) := by
  rintro ⟨publication⟩
  obtain ⟨artifact, present⟩ := publication.approved
  rw [missing] at present
  contradiction

theorem final_requires_durable_recovered_registration
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (publication : Final host template prepare command actual) :
    host.registryRecovered actual ∧ host.registrarCurrent command actual ∧
      ∃ artifact, host.approvedEvidenceAt actual command = some artifact ∧
        host.registrationCommitted actual command artifact := by
  obtain ⟨artifact, present⟩ := publication.approved
  exact ⟨publication.recovered, publication.fenced, artifact, present, publication.durable artifact present⟩

theorem unanchored_registration_cannot_commit
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (missing : ∀ artifact, ¬ host.registrationCommitted actual command artifact) :
    ¬ Nonempty (Final host template prepare command actual) := by
  rintro ⟨publication⟩
  obtain ⟨artifact, _, durable⟩ := (final_requires_durable_recovered_registration publication).2.2
  exact missing artifact durable

theorem unrecovered_registry_cannot_commit
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (missing : ¬ host.registryRecovered actual) :
    ¬ Nonempty (Final host template prepare command actual) := fun ⟨publication⟩ => missing publication.recovered

theorem old_registrar_cannot_commit
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (stale : ¬ host.registrarCurrent command actual) :
    ¬ Nonempty (Final host template prepare command actual) := fun ⟨publication⟩ => stale publication.fenced

theorem stale_use_cannot_commit
    {host : Host Command Result View Parent Artifact Cut}
    {template : Contract Atom Command Result} {command actual}
    (stale : ¬ host.security.currentAtUse actual) :
    ¬ Nonempty (Final host template prepare command actual) :=
  fun ⟨publication⟩ => stale (final_retains_continuous_authorization publication).1

end CedarPooSpec.Gateway.PublicationReview
