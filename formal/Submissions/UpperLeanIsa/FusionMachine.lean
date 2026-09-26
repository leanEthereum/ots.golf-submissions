import Submissions.UpperLeanIsa.FusionMachineFaithful
import Submissions.UpperLeanIsa.FusionMachineTable

/-! The concrete 1149-cycle machine and its machine certificate clauses. -/
namespace OptimalOTS.HLFusion
open OptimalOTS.LeanIsaBaseline.Layer
noncomputable section

/-- The fused OTS, bytecode, memory size, honest prover, and step count. -/
abbrev fusionMachine : LeanIsa.Submission := machineSubmission Fusion.params fusionTab

theorem fusion_faithful : fusionMachine.Faithful := faithful fusionTab_hyp fusion_compat

theorem fusion_sound : fusionMachine.Sound := machine_sound fusionTab_hyp fusion_compat

theorem fusion_cycles : fusionMachine.CyclesAtMost 1149 := machine_cycles fusionTab_hyp

theorem fusion_valid : LeanIsa.BytecodeValid fusionMachine.program := machine_valid

theorem fusion_seededRows : fusionMachine.seededRows < LeanIsa.maxSeededRows := machine_seededRows

end
end OptimalOTS.HLFusion
