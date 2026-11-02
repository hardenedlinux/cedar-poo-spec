import Examples.Enterprise.Payment.PaymentRelease

namespace CedarPooSpec.PaymentReleaseExport

open CedarPooSpec.PaymentReleaseExample

def manifest
    (owner : CedarPooSpec.Functional.Program CedarPooSpec.PaymentReleaseExample.model CedarPooSpec.PaymentReleaseExample.schema :=
      CedarPooSpec.PaymentReleaseExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let operations ← LeanPoo.Functional.Validation.traverse
    (fun (name, root, preparer, releaser, resource, _) =>
      LeanPoo.Functional.Validation.traverse
        (fun (label, input) => owner.case label root.toLower root input entities)
        [(s!"{name}-prepare", request preparer prepare resource),
         (s!"{name}-release", request releaser release resource)]) operationCases
  let branches ← LeanPoo.Functional.Validation.traverse
    (fun (name, root, principal, action, resource, _) =>
      owner.case name root.toLower root (request principal action resource) entities)
    branchCases
  let rows := operations.flatten ++ branches
  return { cases := rows }

end CedarPooSpec.PaymentReleaseExport
