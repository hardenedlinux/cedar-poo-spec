import Examples.Enterprise.Payment.PaymentRelease

namespace CedarPooSpec.PaymentReleaseExport

open CedarPooSpec.PaymentReleaseExample

def manifest : Except String Lean.Json := do
  let operations ← LeanPoo.Functional.Validation.traverse
    (fun (name, root, preparer, releaser, resource, _) =>
      LeanPoo.Functional.Validation.traverse
        (fun (label, input) => program.authorizationCase label root.toLower root input entities)
        [(s!"{name}-prepare", request preparer prepare resource),
         (s!"{name}-release", request releaser release resource)]) operationCases
  let branches ← LeanPoo.Functional.Validation.traverse
    (fun (name, root, principal, action, resource, _) =>
      program.authorizationCase name root.toLower root (request principal action resource) entities)
    branchCases
  let rows := operations.flatten ++ branches
  return Lean.Json.mkObj [("cases", Lean.toJson rows)]

end CedarPooSpec.PaymentReleaseExport
