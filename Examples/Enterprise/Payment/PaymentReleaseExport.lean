import Examples.Enterprise.Payment.PaymentRelease

namespace CedarPooSpec.PaymentReleaseExport

open CedarPooSpec.PaymentReleaseExample

def manifest : Except String CedarPooSpec.Transport.Manifest := do
  let operations ← LeanPoo.Functional.Validation.traverse
    (fun (name, root, preparer, releaser, resource, _) =>
      LeanPoo.Functional.Validation.traverse
        (fun (label, input) => program.case label root.toLower root input entities)
        [(s!"{name}-prepare", request preparer prepare resource),
         (s!"{name}-release", request releaser release resource)]) operationCases
  let branches ← LeanPoo.Functional.Validation.traverse
    (fun (name, root, principal, action, resource, _) =>
      program.case name root.toLower root (request principal action resource) entities)
    branchCases
  let rows := operations.flatten ++ branches
  return { cases := rows }

end CedarPooSpec.PaymentReleaseExport
