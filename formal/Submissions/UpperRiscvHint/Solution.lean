import Submissions.UpperRiscvHint.HintView

namespace OptimalOTS.Challenge.UpperRiscvHint
open RiscvMixedProgram

/-- The fixed-length completion scheme, with full disclosures supplied in the machine view. -/
noncomputable def submission : RiscvHint.Submission :=
  HintTrap.submission Completion.scheme image viewCompress layoutView rawView 1337

theorem certificate : submission.Certificate 310 :=
  HintTrap.certificate Completion.scheme image viewCompress layoutView rawView 1337 trapVerify 310
    Completion.admissible Completion.secure image_valid
    (fun pk m v n h => (image_refines_trap pk m v n h).1)
    (fun pk m v n h => (image_refines_trap pk m v n h).2)
    layoutView_compress raw_compress trap_sound trap_raw trap_accepts

theorem image_size : submission.image.byteSize < 1048576 := RiscvMixedProgram.image_size
end OptimalOTS.Challenge.UpperRiscvHint
