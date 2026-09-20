import OptimalOTS.Riscv
import Submissions.UpperRiscv.Wire
import Submissions.UpperRiscv.Verifier

/-! The proved OTS specification and its RV64IM implementation. -/

namespace OptimalOTS.RiscvUpperForest

open OracleComp

noncomputable def submission : Riscv.Submission where
  scheme := Wire.scheme
  image := Riscv2Program.image
  fuel := fun _ _ _ => 1337

theorem submission_scheme : submission.scheme = Wire.scheme := rfl

theorem submission_admissible : submission.scheme.Admissible := by
  rw [submission_scheme]
  exact Wire.admissible

theorem submission_secure : submission.scheme.Secure := by
  rw [submission_scheme]
  exact Wire.secure

/-- The machine's complete oracle computation is the certified verifier on every input, so
every execution terminates within the fixed fuel and issues exactly the specified queries. -/
theorem submission_implements : submission.Implements := by
  refine ⟨Riscv2Program.image_valid, fun pk m bits => ?_⟩
  change Riscv.observe 1337 (Riscv.initialState Riscv2Program.image pk m bits) =
    some <$> Wire.scheme.verify pk m bits
  rw [(Riscv2Program.image_refines pk m bits).1, ForestVerifier.directVerify_eq]

/-- Every run, accepting or rejecting, executes at most 436 cycles: one per executed
instruction and eleven for the 5440-bit root hash, with the chain steps charged by the path
taken. -/
theorem submission_cycles : submission.CyclesAtMost 436 := by
  intro pk m bits b cycles completed
  exact (Riscv2Program.image_refines pk m bits).2 b cycles completed

/-- Every requirement of a scored RISC-V submission, at 436 cycles. -/
theorem machineCertificate : submission.Certificate 436 :=
  ⟨submission_admissible, submission_secure, submission_implements, submission_cycles⟩

/--
info: 'OptimalOTS.RiscvUpperForest.machineCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms machineCertificate

end OptimalOTS.RiscvUpperForest
