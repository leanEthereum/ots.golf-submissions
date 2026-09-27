import Submissions.UpperLeanIsa.FusionMachineFaithful
import Submissions.UpperLeanIsa.FusionMachineTable
import Submissions.UpperLeanIsa.FusionSecurity
import Submissions.UpperLeanIsa.FusionAdmissible

/-! The concrete 1125-cycle machine and its machine certificate clauses. -/
namespace OptimalOTS.HLFusion
open OptimalOTS.LeanIsaBaseline.Layer
noncomputable section

/-- The fused OTS, bytecode, memory size, honest prover, and step count. -/
abbrev fusionMachine : LeanIsa.Submission := machineSubmission Fusion.params fusionTab

theorem fusion_faithful : fusionMachine.Faithful := faithful fusionTab_hyp fusion_compat

theorem fusion_sound : fusionMachine.Sound := machine_sound fusionTab_hyp fusion_compat

theorem fusion_cycles : fusionMachine.CyclesAtMost 1125 := machine_cycles fusionTab_hyp

theorem fusion_valid : LeanIsa.BytecodeValid fusionMachine.program := machine_valid

theorem fusion_seededRows : fusionMachine.seededRows < LeanIsa.maxSeededRows := machine_seededRows

end
end OptimalOTS.HLFusion

/-! The 1125-cycle leanISA submission: nine groups bind chain endpoints, five with five-dep
fused packets and four with three-dep packets, one hash finishes the root, and a landing
checksum forces 86 chain steps.
The certificate includes the exact rarest-cut signing bound and strong unforgeability. -/

namespace OptimalOTS.Challenge.UpperLeanIsa

open OptimalOTS OptimalOTS.LeanIsaBaseline.Layer

/-- The OTS, the bytecode, the announced memory size, the prover's memory-filling strategy and
the step count. -/
noncomputable def submission : LeanIsa.Submission := HLFusion.fusionMachine

/-- Admissibility and strong security of the OTS, well-formed bytecode, agreement of the honest
prover's run with the verifier, soundness against every prover-chosen memory, and at most
`1125` cycles on every completing execution. -/
theorem certificate : submission.Certificate 1125 where
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
