import Submissions.UpperRiscvHint.Wire
import Submissions.UpperRiscvHint.Program

/-! Exact signature layout used by the assembly refinement. -/

noncomputable section
open scoped Classical

namespace OptimalOTS.Forest

open OptimalOTS.Dag


def fullSignatureBits (index : ChainIndex) : ℕ :=
  5495 + if (fixedChoice index 32).val = 31 then 3 else 0

theorem fixed_revealBits (i : Idx) :
    forestScheme.graph.revealBits (forestScheme.sets i) = fullSignatureBits i - 128 := by
  change graph.revealBits (fins (cutOf (fixedChoice i))) = fullSignatureBits i - 128
  rw [revealBits_eq, reveal_cutOf_exact]
  unfold fullSignatureBits
  split_ifs <;> omega

end OptimalOTS.Forest

namespace OptimalOTS.RiscvUpperForest.Wire

open OptimalOTS.Dag


/-- The full signature length is the nonce plus the index-dependent disclosure length. -/
theorem payload_length_iff (bits : List Bool) (i : Idx) :
    (decode bits).2.length = Forest.forestScheme.graph.revealBits (Forest.forestScheme.sets i) ↔
      bits.length = Forest.fullSignatureBits i := by
  rw [Forest.fixed_revealBits]
  simp only [decode, List.length_drop]
  unfold Forest.fullSignatureBits
  split_ifs <;> omega

end OptimalOTS.RiscvUpperForest.Wire
