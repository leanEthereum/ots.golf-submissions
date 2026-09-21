import Submissions.UpperRiscv.Candidate

/-! A bare-chain forest OTS with an equivalent RV64IM verifier, at most 394 cycles on every
execution. -/

namespace OptimalOTS.Challenge.UpperRiscv

/-- The OTS algorithms, fixed machine image, and termination witness. -/
noncomputable def submission : Riscv.Submission := RiscvUpperForest.submission

/-- Correctness, signing availability, resource limits, 127-bit strong security, exact machine
refinement on every input, and at most 394 cycles on every execution. -/
theorem certificate : submission.Certificate 394 := RiscvUpperForest.machineCertificate

/-- Instructions and embedded data together occupy strictly less than 1 MiB: `4 · 12494 + 104`
bytes. -/
theorem image_size : submission.image.byteSize < 1048576 := by
  have hi : submission.image = Riscv2Program.image := rfl
  have hd : Riscv2Program.image.data = Riscv2Program.dataImage := rfl
  rw [Riscv.Image.byteSize, hi, Riscv2Program.image_code, hd, Riscv2Program.verifier_length,
    Riscv2Program.dataImage_length]
  norm_num

end OptimalOTS.Challenge.UpperRiscv
