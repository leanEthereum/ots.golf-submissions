import Submissions.UpperLeanIsa.Security
import Submissions.UpperLeanIsa.MachineFaithful

/-! The leanISA baseline: the Winternitz scheme of `Algorithms.lean`, its straight-line bytecode
(`MachineProgram.lean`) and the six certificate clauses. -/

namespace OptimalOTS.Challenge.UpperLeanIsa

open OptimalOTS OptimalOTS.LeanIsaBaseline

/-- The OTS, the bytecode, the announced memory size, the prover's memory-filling strategy and
the step count. -/
noncomputable def submission : LeanIsa.Submission := Honest.machineSubmission

/-- Admissibility and strong security of the OTS, well-formed bytecode, agreement of the honest
prover's run with the verifier, soundness against every prover-chosen memory, and at most
`170549` cycles on every completing execution. -/
theorem certificate : submission.Certificate 170549 where
  admissible := LeanIsaBaseline.admissible
  secure := LeanIsaBaseline.secure
  valid := Machine.valid
  faithful := Honest.faithful
  sound := Honest.sound submission rfl rfl
  cycles := by
    have h := Machine.cycles submission rfl
    rwa [Machine.claim_eq] at h

/-- The bytecode slots and memory cells the prover must seed and finalize, together fewer than
`LeanIsa.maxSeededRows`. -/
theorem seeded_rows : submission.seededRows < LeanIsa.maxSeededRows :=
  Machine.seededRows_lt submission rfl rfl

end OptimalOTS.Challenge.UpperLeanIsa
