import Submissions.UpperLeanIsa.FourSecurity
import Submissions.UpperLeanIsa.FourAdmissible
import Submissions.UpperLeanIsa.FourMachine

/-! The 1125-cycle leanISA submission: nine groups bind four dependency tops each
through their final chain hashes, one hash finishes the root, and a landing checksum
forces 86 chain steps. Fourteen constants serve the frames, costs and domain words.
The certificate includes the exact rarest-cut signing bound and strong unforgeability. -/

namespace OptimalOTS.Challenge.UpperLeanIsa

open OptimalOTS OptimalOTS.LeanIsaBaseline.Layer

/-- The OTS, the bytecode, the announced memory size, the prover's memory-filling strategy and
the step count. -/
noncomputable def submission : LeanIsa.Submission := HLFour.fusionMachine

/-- Admissibility and strong security of the OTS, well-formed bytecode, agreement of the honest
prover's run with the verifier, soundness against every prover-chosen memory, and at most
`1125` cycles on every completing execution. -/
theorem certificate : submission.Certificate 1125 where
  admissible := FourFusion.concrete_admissible
  secure := FourFusion.concrete_secure
  valid := HLFour.fusion_valid
  faithful := HLFour.fusion_faithful
  sound := HLFour.fusion_sound
  cycles := HLFour.fusion_cycles

/-- The bytecode slots and memory cells the prover must seed and finalize, together fewer than
`LeanIsa.maxSeededRows`. -/
theorem seeded_rows : submission.seededRows < LeanIsa.maxSeededRows := HLFour.fusion_seededRows

end OptimalOTS.Challenge.UpperLeanIsa
