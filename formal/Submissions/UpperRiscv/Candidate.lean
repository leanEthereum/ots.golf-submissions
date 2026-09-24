import OptimalOTS.Riscv
import Submissions.UpperRiscv.Wire
import Submissions.UpperRiscv.MixedVerifier

/-! The proved OTS specification and its RV64IM implementation. -/

namespace OptimalOTS.RiscvUpperForest

open OracleComp

noncomputable def submission : Riscv.Submission where
  scheme := RiscvMixedProgram.stagedScheme
  image := RiscvMixedProgram.image
  fuel := fun _ _ _ => 1337

theorem submission_scheme : submission.scheme = RiscvMixedProgram.stagedScheme := rfl

theorem submission_admissible : submission.scheme.Admissible := by
  rw [submission_scheme]
  exact RiscvMixedProgram.stagedScheme_admissible

theorem submission_secure : submission.scheme.Secure := by
  rw [submission_scheme]
  exact RiscvMixedProgram.stagedScheme_secure

/-- The machine's complete oracle computation is the certified verifier on every input, so
every execution terminates within the fixed fuel and issues exactly the specified queries. -/
theorem submission_implements : submission.Implements := by
  refine ⟨RiscvMixedProgram.image_valid, fun pk m bits => ?_⟩
  change Riscv.observe 1337 (Riscv.initialState RiscvMixedProgram.image pk m bits) =
    some <$> RiscvMixedProgram.stagedVerify pk m bits
  exact (RiscvMixedProgram.image_refines pk m bits).1

/-- Every accepting or rejecting run costs at most 349 cycles: 33 for index processing,
295 for all chain blocks, and 21 for the root and decision. -/
theorem submission_cycles : submission.CyclesAtMost 349 := by
  intro pk m bits b cycles completed
  exact (RiscvMixedProgram.image_refines pk m bits).2 b cycles completed

/-- Every requirement of a scored RISC-V submission, at 349 cycles. -/
theorem machineCertificate : submission.Certificate 349 :=
  ⟨submission_admissible, submission_secure, submission_implements, submission_cycles⟩

/--
info: 'OptimalOTS.RiscvUpperForest.machineCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms machineCertificate

end OptimalOTS.RiscvUpperForest
