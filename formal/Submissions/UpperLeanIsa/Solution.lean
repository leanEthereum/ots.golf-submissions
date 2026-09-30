import Submissions.UpperLeanIsa.FreeLastFaithful

/-! The 1088-cycle leanISA submission. Three landing hints and a free-last
execution order implement a layer-85 scheme with four internal children.
The certificate covers security, the honest prover, all committed images, and
the complete execution cost including the public-boundary charge. -/

namespace OptimalOTS.Challenge.UpperLeanIsa

open OptimalOTS OptimalOTS.LeanIsaBaseline.Layer

/-- The OTS, the bytecode, the announced memory size, the prover's memory-filling strategy and
the step count. -/
noncomputable def submission : LeanIsa.Submission := FreeLastVM.freeLastMachine

/-- Admissibility and strong security of the OTS, well-formed bytecode, agreement of the honest
prover's run with the verifier, soundness against every prover-chosen memory, and at most
`1088` cycles on every completing execution. -/
theorem certificate : submission.Certificate 1088 := FreeLastVM.freeLast_certificate

/-- The bytecode slots and memory cells the prover must seed and finalize, together fewer than
`LeanIsa.maxSeededRows`. -/
theorem seeded_rows : submission.seededRows < LeanIsa.maxSeededRows := FreeLastVM.freeLast_seededRows

end OptimalOTS.Challenge.UpperLeanIsa
