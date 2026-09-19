import Submissions.UpperRiscv.Wire
import Submissions.UpperRiscv.Program

/-! Exact signature layout and table bounds used by the assembly refinement. -/

noncomputable section
open scoped Classical

namespace OptimalOTS.Forest

open OptimalOTS.Dag


theorem fixed_revealBits (i : Idx) :
    forestScheme.graph.revealBits (forestScheme.sets i) = 4096 := by
  change graph.revealBits (fins (cutOf (fixedChoice i))) = 4096
  rw [revealBits_eq, Finset.sum_const_nat (fun n hn => (fixedCut_isCut i).values n hn),
    fixedCut_card]

end OptimalOTS.Forest

namespace OptimalOTS.RiscvUpperForest.Wire

open OptimalOTS.Dag


/-- The machine's fixed-length check is exactly the specification's payload-length check. -/
theorem payload_length_iff (bits : List Bool) (i : Idx) :
    (decode bits).2.length = Forest.forestScheme.graph.revealBits (Forest.forestScheme.sets i) ↔
      bits.length = 4224 := by
  rw [Forest.fixed_revealBits]
  simp only [decode, List.length_drop]
  omega

end OptimalOTS.RiscvUpperForest.Wire
