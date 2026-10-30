import CedarPooSpec.Data.DerivedArtifact
import CedarPooSpec.Functional.ObjectProfile

/-! Typed composition of actual source labels and a derived artifact digest.
Origin authentication and physical transformation remain Host responsibilities. -/
namespace CedarPooSpec.Data.LineageProfile
open LeanPoo.Functional.ObjectContract

inductive Key where
  | sources | digest | artifact
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
abbrev Value : Key → Type
  | .sources => List SourceLabel
  | .digest => String
  | .artifact => DerivedArtifact
abbrev Object := LeanPoo.Object.Dataflow.Instance Key Value

def contract : Contract Object Key Unit String :=
  refine (Functional.ObjectProfile.shape [.sources, .digest, .artifact]) fun profile path =>
    match profile.read .sources, profile.read .digest, profile.read .artifact with
    | some sources, some digest, some artifact =>
      if !digest.isEmpty && !sources.isEmpty && decide (artifact = { digest, sources }) then []
      else [.rejected path "lineage projection mismatch"]
    | _, _, _ => [.rejected path "missing lineage projection"]

def artifact? (profile : Object) : Option DerivedArtifact :=
  Functional.ObjectProfile.read contract profile .artifact

theorem artifact_requires_contract (profile : Object) (artifact : DerivedArtifact)
    (accepted : artifact? profile = some artifact) : diagnose contract profile [] = [] :=
  Functional.ObjectProfile.read_requires_contract contract profile _ _ accepted
end CedarPooSpec.Data.LineageProfile
