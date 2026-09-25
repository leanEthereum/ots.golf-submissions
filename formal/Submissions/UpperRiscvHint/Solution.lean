import Submissions.UpperRiscvHint.HintPort

namespace OptimalOTS.Challenge.UpperRiscvHint
/-- The record verifier with identity signature views and no hinting. -/
noncomputable def submission : RiscvHint.Submission := RiscvUpperForest.submission.hinted

theorem certificate : submission.Certificate 349 :=
  RiscvUpperForest.submission.hinted_certificate RiscvUpperForest.machineCertificate
    RiscvMixedProgram.long_view_rejects

theorem image_size : submission.image.byteSize < 1048576 := RiscvMixedProgram.image_size
end OptimalOTS.Challenge.UpperRiscvHint
