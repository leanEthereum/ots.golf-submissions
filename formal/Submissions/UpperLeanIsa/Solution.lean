import Submissions.UpperLeanIsa.AffineMachine

/-! The 1110-cycle leanISA submission. Affine destination-dependent frames remove
fourteen entry jumps while preserving the layer-86 four-child binding scheme.
The certificate covers security, the honest prover, all committed images, and
the complete execution cost including the public-boundary charge. -/

namespace OptimalOTS.Challenge.UpperLeanIsa

open OptimalOTS OptimalOTS.LeanIsaBaseline.Layer

/-- The OTS, the bytecode, the announced memory size, the prover's memory-filling strategy and
the step count. -/
noncomputable def submission : LeanIsa.Submission := AffineVM.affineMachine

/-- Admissibility and strong security of the OTS, well-formed bytecode, agreement of the honest
prover's run with the verifier, soundness against every prover-chosen memory, and at most
`1110` cycles on every completing execution. -/
theorem certificate : submission.Certificate 1110 := AffineVM.affine_certificate

/-- The bytecode slots and memory cells the prover must seed and finalize, together fewer than
`LeanIsa.maxSeededRows`. -/
theorem seeded_rows : submission.seededRows < LeanIsa.maxSeededRows := AffineVM.affine_seededRows

end OptimalOTS.Challenge.UpperLeanIsa
