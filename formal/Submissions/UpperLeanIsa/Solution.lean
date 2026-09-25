import Submissions.UpperLeanIsa.FusionSecurity
import Submissions.UpperLeanIsa.FusionAdmissible
import Submissions.UpperLeanIsa.FusionMachine

/-! The 1149-cycle leanISA submission: six groups fuse chain endpoints with dependency
binding, three hashes finish the root, and a landing checksum forces 86 chain steps.
The certificate includes the exact rarest-cut signing bound and strong unforgeability. -/

namespace OptimalOTS.Challenge.UpperLeanIsa

open OptimalOTS OptimalOTS.LeanIsaBaseline.Layer

/-- The OTS, the bytecode, the announced memory size, the prover's memory-filling strategy and
the step count. -/
noncomputable def submission : LeanIsa.Submission := HLFusion.fusionMachine

/-- Admissibility and strong security of the OTS, well-formed bytecode, agreement of the honest
prover's run with the verifier, soundness against every prover-chosen memory, and at most
`1149` cycles on every completing execution. -/
theorem certificate : submission.Certificate 1149 where
  admissible := Fusion.concrete_admissible
  secure := Fusion.concrete_secure
  valid := HLFusion.fusion_valid
  faithful := HLFusion.fusion_faithful
  sound := HLFusion.fusion_sound
  cycles := HLFusion.fusion_cycles

/-- The bytecode slots and memory cells the prover must seed and finalize, together fewer than
`LeanIsa.maxSeededRows`. -/
theorem seeded_rows : submission.seededRows < LeanIsa.maxSeededRows := HLFusion.fusion_seededRows

end OptimalOTS.Challenge.UpperLeanIsa
