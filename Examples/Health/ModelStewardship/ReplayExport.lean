import CedarPooSpec.Functional.Capabilities
import Examples.Health.ModelStewardship.Admission

/-! Replay the exact operation projections checked through BoundOperation. -/

namespace CedarPooSpec.ModelStewardshipExample.ReplayExport

open CedarPooSpec.ModelStewardshipExample
open CedarPooSpec.ModelStewardshipExample.Admission

def manifest
    (owner : CedarPooSpec.Functional.Compilation CedarPooSpec.ModelStewardshipExample.model :=
      CedarPooSpec.ModelStewardshipExample.program) : Except String CedarPooSpec.Transport.Manifest := do
  let cases : List (String × String × Effect × Snapshot) := [
    ("train-approved", "MedicalModel", trainingEffect, trainingSnapshot),
    ("train-swapped-source", "MedicalModel",
      { trainingEffect with source := independentModel }, trainingSnapshot),
    ("train-revoked-grant", "MedicalModel", trainingEffect,
      { trainingSnapshot with governanceRevision := 2 }),
    ("train-missing-assessment", "MedicalModel", trainingEffect,
      { trainingSnapshot with assessment := none }),
    ("train-wrong-assessor", "MedicalModel", trainingEffect,
      { trainingSnapshot with assessment := some { deidentificationAssessment with assessor := releaseReviewer } }),
    ("train-wrong-approver", "MedicalModel", trainingEffect,
      { trainingSnapshot with grant := some { trainingGrant with approver := releaseReviewer } }),
    ("train-other-digest", "MedicalModel",
      { trainingEffect with sourceDigest := "other-dataset-bytes" }, trainingSnapshot),
    ("train-withdrawn-source", "MedicalModel", trainingEffect,
      { trainingSnapshot with withdrawn := ["hospital-b-record"] }),
    ("publish-approved", "MedicalModel", publicationEffect, publicationSnapshot),
    ("publish-other-sink", "MedicalModel",
      { publicationEffect with target := independentEndpoint }, publicationSnapshot),
    ("publish-unreviewed", "MedicalModel", publicationEffect,
      { publicationSnapshot with assessment := none }),
    ("publish-other-digest", "MedicalModel",
      { publicationEffect with sourceDigest := "modified-model-bytes" }, publicationSnapshot),
    ("publish-withdrawn-source", "MedicalModel", publicationEffect,
      { publicationSnapshot with withdrawn := ["hospital-b-record"] }),
    ("publish-stale-catalog", "MedicalModel", publicationEffect,
      { publicationSnapshot with catalogRevision := "r2" }),
    ("infer-approved", "MedicalModel", inferenceEffect, inferenceSnapshot),
    ("infer-wrong-patient", "MedicalModel",
      { inferenceEffect with patient := some "patient-43" }, inferenceSnapshot),
    ("infer-withdrawn-source", "MedicalModel", inferenceEffect,
      { inferenceSnapshot with withdrawn := ["hospital-b-record"] }),
    ("incident-training", "ModelIncident", trainingEffect, trainingSnapshot),
    ("incident-publish", "ModelIncident", publicationEffect, publicationSnapshot),
    ("incident-infer", "ModelIncident", inferenceEffect, inferenceSnapshot),
    ("recovered-publish", "Recovered", publicationEffect, publicationSnapshot),
    ("recovered-infer", "Recovered", inferenceEffect, inferenceSnapshot)]
  let rows ← cases.mapM fun (name, root, effect, snapshot) =>
    owner.case
        name root root (operationRequest effect snapshot) (entities snapshot.lineageRevision)
  return { cases := rows }

end CedarPooSpec.ModelStewardshipExample.ReplayExport
