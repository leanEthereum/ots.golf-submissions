import Submissions.UpperRiscvHint.HintView

namespace OptimalOTS.Challenge.UpperRiscvHint
open RiscvMixedProgram

/-- The free-chain scheme's signatures, laid out in place with their free count when accepted and
in the raw form otherwise, read by the 311-cycle trapping image. -/
noncomputable def submission : RiscvHint.Submission :=
  HintTrap.submission stagedScheme image viewCompress layoutView rawView 1337

theorem certificate : submission.Certificate 311 :=
  HintTrap.certificate stagedScheme image viewCompress layoutView rawView 1337 trapVerify 311
    stagedScheme_admissible stagedScheme_secure image_valid
    (fun pk m v n h => (image_refines_trap pk m v n h).1)
    (fun pk m v n h => (image_refines_trap pk m v n h).2)
    layoutView_compress raw_compress trap_sound trap_raw trap_accepts

theorem image_size : submission.image.byteSize < 1048576 := RiscvMixedProgram.image_size
end OptimalOTS.Challenge.UpperRiscvHint
