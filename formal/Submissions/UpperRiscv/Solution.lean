import Submissions.UpperRiscv.Candidate

/-! A flat forest OTS with an equivalent RV64IM verifier, at most 702 cycles on every execution. -/

namespace OptimalOTS.Challenge.UpperRiscv

/-- The OTS algorithms, fixed machine image, and termination witness. -/
noncomputable def submission : Riscv.Submission := RiscvUpperForest.submission

/-- Correctness, signing availability, resource limits, 127-bit strong security, exact machine
refinement on every input, and at most 702 cycles on every execution. -/
theorem certificate : submission.Certificate 702 := RiscvUpperForest.machineCertificate

end OptimalOTS.Challenge.UpperRiscv
