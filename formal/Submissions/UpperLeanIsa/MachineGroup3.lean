import Submissions.UpperLeanIsa.MachineFaithful
import Submissions.UpperLeanIsa.MachineTable

/-! The concrete 1281-cycle machine and its certificate clauses. -/
namespace OptimalOTS.HLG3
open OptimalOTS.LeanIsaBaseline.Layer
noncomputable section

/-! ## The machine clauses for the GROUP-3 scheme -/

/-- The HL-GROUP-3 machine submission. -/
abbrev g3machine : LeanIsa.Submission := machineSubmission Group3.params g3tab

theorem g3_faithful : g3machine.Faithful := faithful g3tab_hyp g3_compat

theorem g3_sound : g3machine.Sound := machine_sound g3tab_hyp g3_compat

theorem g3_cycles : g3machine.CyclesAtMost 1281 := machine_cycles g3tab_hyp

theorem g3_valid : LeanIsa.BytecodeValid g3machine.program := machine_valid

theorem g3_seededRows : g3machine.seededRows < LeanIsa.maxSeededRows := machine_seededRows

end

end OptimalOTS.HLG3
