import CedarPooSpec.Functional.Capabilities
import Examples.Enterprise.Agent.Department.Simulation

namespace CedarPooSpec.DepartmentSynthesisValidatedExport

open CedarPooSpec.DepartmentSynthesisExample

/-- Export the exact context supplied at each pre-admission boundary. -/
def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let mut rows : List CedarPooSpec.Transport.Case := []
  for (name, root, state, attempts, _) in cases do
    for ((req, _), index) in (replay root state attempts).1.zipIdx do
      let row ← CedarPooSpec.DepartmentSynthesisExample.program.case
          s!"{name}-step-{index}" root root req entities
      rows := rows ++ [row]
  CedarPooSpec.SchemaJson.manifest schema rows

end CedarPooSpec.DepartmentSynthesisValidatedExport
