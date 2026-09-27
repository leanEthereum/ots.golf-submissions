import Submissions.UpperRiscvHint.HintView

namespace OptimalOTS.Challenge.UpperRiscvHint
open RiscvMixedProgram

/-- The cap-chain scheme's signatures, laid out in place when accepted and in the raw form
otherwise, read by the 324-cycle trapping image. -/
noncomputable def submission : RiscvHint.Submission :=
  HintTrap.submission stagedScheme image viewCompress honestView rawView 1337

theorem certificate : submission.Certificate 324 :=
  HintTrap.certificate stagedScheme image viewCompress honestView rawView 1337 trapVerify 324
    stagedScheme_admissible stagedScheme_secure image_valid
    (fun pk m v n h => (image_refines_trap pk m v n h).1)
    (fun pk m v n h => (image_refines_trap pk m v n h).2)
    (fun pk m σ h => layout_compress σ (by
      by_contra hl
      exact absurd (stagedVerify_short pk m σ hl true h) (by simp)))
    raw_compress trap_sound trap_raw trap_accepts

theorem image_size : submission.image.byteSize < 1048576 := RiscvMixedProgram.image_size
end OptimalOTS.Challenge.UpperRiscvHint
