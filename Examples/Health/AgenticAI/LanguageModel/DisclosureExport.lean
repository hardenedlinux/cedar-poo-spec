import CedarPooSpec.SchemaJson
import Examples.Health.AgenticAI.LanguageModel.Disclosure

/-! The same synthetic requests and composed policy roots are replayed by
the official Cedar Rust validator and authorizer. -/

namespace CedarPooSpec.AgenticAI.LanguageModel.DisclosureExport

open CedarPooSpec.AgenticAI.LanguageModel.Disclosure

def manifest : Except String Lean.Json := do
  let rows ← LeanPoo.Functional.Validation.traverse (fun (name, root, state, effect, _) =>
    program.authorizationCase name root
      root (projectedRequest state effect) publicationEntities) Disclosure.cases
  CedarPooSpec.SchemaJson.validatedManifest publicationSchema rows

end CedarPooSpec.AgenticAI.LanguageModel.DisclosureExport
