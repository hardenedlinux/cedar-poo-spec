import CedarPooSpec.SchemaJson
import Examples.Health.AgenticAI.LanguageModel.Disclosure

/-! The same synthetic requests and composed policy roots are replayed by
the official Cedar Rust validator and authorizer. -/

namespace CedarPooSpec.AgenticAI.LanguageModel.DisclosureExport

open CedarPooSpec.AgenticAI.LanguageModel.Disclosure

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationModel CedarPooSpec.AgenticAI.LanguageModel.Disclosure.publicationSchema :=
      CedarPooSpec.AgenticAI.LanguageModel.Disclosure.program) : Except String CedarPooSpec.Transport.Manifest := do
  let rows ← LeanPoo.Functional.Validation.traverse (fun (name, root, state, effect, _) =>
    owner.case name root
      root (projectedRequest state effect) publicationEntities) Disclosure.cases
  CedarPooSpec.SchemaJson.manifest publicationSchema rows

end CedarPooSpec.AgenticAI.LanguageModel.DisclosureExport
