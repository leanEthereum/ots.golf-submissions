import Submissions.UpperRiscv.MixedDispatchArith
import Submissions.UpperRiscv.MixedContext

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program
open OptimalOTS.Dag

/-- Halfword extraction needs only a single abstract word of memory. -/
theorem stored_lane_extract (s : MachineState) (q : Fin 16) (v : Word)
    (stored : s.getMem (W (laneWordAddr (laneGroup q))) = v) :
    (s.getHalfword (W (laneAddr q))).toNat =
      v.toNat / 2 ^ (16 * laneIdx q) % 2 ^ 16 := by
  have hq := q.isLt
  have hl : laneIdx q < 4 := by unfold laneIdx; omega
  have hg : laneGroup q < 4 := by unfold laneGroup; omega
  have addr : laneAddr q = laneWordAddr (laneGroup q) + 2 * laneIdx q := by
    unfold laneAddr laneWordAddr laneGroup laneIdx
    omega
  calc
    _ = (s.getMem (W (laneWordAddr (laneGroup q)))).toNat /
        2 ^ (16 * laneIdx q) % 2 ^ 16 := by
      rw [addr]
      exact getHalfword_lane s _ _ (by unfold laneWordAddr laneBase; omega) hl
        (by unfold laneWordAddr laneBase; omega)
    _ = _ := congrArg (fun w : Word => w.toNat / 2 ^ (16 * laneIdx q) % 2 ^ 16) stored

end OptimalOTS.RiscvMixedProgram
