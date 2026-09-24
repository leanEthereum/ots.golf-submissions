import Submissions.UpperRiscv.Candidate

/-! A capped-rank forest OTS with an equivalent RV64IM verifier, at most 349 cycles on every
execution. -/

namespace OptimalOTS.Challenge.UpperRiscv

/-- The OTS algorithms, fixed machine image, and termination witness. -/
noncomputable def submission : Riscv.Submission := RiscvUpperForest.submission

/-- Correctness, signing availability, resource limits, 127-bit strong security, exact machine
refinement on every input, and at most 349 cycles on every execution. -/
theorem certificate : submission.Certificate 349 := RiscvUpperForest.machineCertificate

/-- The fixed image occupies 62,892 bytes, strictly less than 1 MiB. -/
theorem image_size : submission.image.byteSize < 1048576 := RiscvMixedProgram.image_size

end OptimalOTS.Challenge.UpperRiscv
