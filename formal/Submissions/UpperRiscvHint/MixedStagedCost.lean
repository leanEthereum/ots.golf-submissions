import Submissions.UpperRiscvHint.MixedPair
import Submissions.UpperRiscvHint.MixedIndexArith
import Submissions.UpperRiscvHint.CappedCost

namespace OptimalOTS.RiscvMixedProgram

def pairWeight (index : RawIdx) (q : ℕ) : ℕ :=
  digit index.val (2*q) + digit index.val (2*q+1)

theorem pairCost_overhead (index : RawIdx) (q : Fin 16) :
    pairCost index q = CappedCost.overhead q.val + pairWeight index q.val := by
  have h : (lengthSetup q).length + 8 = CappedCost.overhead q.val + 2 * lead q := by
    revert q
    decide +kernel
  rw [pairCost_eq, remaining_left, remaining_right]
  have hl := lead_le q
  unfold pairWeight
  omega

theorem badPairCost_eq (q : Fin 16) : badPairCost q = CappedCost.rejectCost q.val := by
  unfold badPairCost
  rw [dispatchCode_length]
  revert q
  decide +kernel

theorem stagedCost_eq (index : RawIdx) (n q : ℕ) (hq : q+n ≤ 16) :
    stagedCost index n q = CappedCost.cost (pairWeight index) n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [stagedCost, dif_pos (show q < 16 by omega), CappedCost.cost]
    change (if pairWeight index q ≤ PairCode.cap q then
      pairCost index ⟨q, by omega⟩ + stagedCost index n (q+1) else badPairCost ⟨q, by omega⟩) = _
    split_ifs
    · rw [pairCost_overhead, ih (q+1) (by omega)]
    · exact badPairCost_eq _

theorem stagedCost_le (index : RawIdx) : stagedCost index 16 0 ≤ 549 := by
  rw [stagedCost_eq index 16 0 (by decide)]
  exact CappedCost.cost_le _ 16 0

/-- When every pair passes, the pairs, the root and the decision cost 138 cycles besides the
digit sum. -/
theorem stagedCost_allowed (index : RawIdx) (caps : ∀ q : Fin 16, PairAllowed index.val q) :
    stagedCost index 16 0 = 138 + digitSum index.val := by
  rw [stagedCost_eq index 16 0 (by decide), CappedCost.cost_allowed]
  · unfold digitSum
    have h := sum_digit_pairs (digit index.val) 16
    rw [show 2 * 16 = 32 from rfl] at h
    rw [h]
    rfl
  · intro q hq
    exact caps ⟨q, hq⟩

end OptimalOTS.RiscvMixedProgram
