import Submissions.UpperRiscvHint.MixedPair
import Submissions.UpperRiscvHint.MixedIndexArith
import Submissions.UpperRiscvHint.CappedCost

namespace OptimalOTS.RiscvMixedProgram

def pairWeight (index : RawIdx) (q : ℕ) : ℕ :=
  digit index.val (2*q) + digit index.val (2*q+1)

theorem pairCost_overhead (index : RawIdx) (q : Fin 16) :
    pairCost index q = CappedCost.overhead q.val + pairWeight index q.val := by
  have h : (lengthSetup q).length + (if q.val = 0 then 1 else 0) + 8 =
      CappedCost.overhead q.val + 2 * lead q := by
    revert q
    decide +kernel
  rw [pairCost_eq, steps_eq_digit, steps_eq_digit]
  dsimp only [pairWeight, leftChain, rightChain] at *
  unfold lead at h
  have hA := digit_lt_16 index.val (2*q.val)
  have hB := digit_lt_16 index.val (2*q.val+1)
  by_cases hq8 : q.val < 8
  · simp only [hq8, show 2*q.val < 16 by omega, show 2*q.val+1 < 16 by omega, if_true] at h ⊢
    omega
  · simp only [hq8, show ¬ 2*q.val < 16 by omega, show ¬ 2*q.val+1 < 16 by omega, if_false] at h ⊢
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

/-- Every chain/root path fits in 293 cycles, including the first forbidden pair. -/
theorem stagedCost_le (index : RawIdx) (rank : IndexRank index.val) :
    stagedCost index 16 0 ≤ 293 := by
  rw [stagedCost_eq index 16 0 (by decide)]
  apply CappedCost.bound
  · intro q _
    have ha := digit_lt_16 index.val (2*q)
    have hb := digit_lt_16 index.val (2*q+1)
    unfold pairWeight
    omega
  · unfold IndexRank at rank
    have hs : (∑ k ∈ Finset.range 32, digit index.val k) =
        ∑ q ∈ Finset.range 16, pairWeight index q := sum_digit_pairs (digit index.val) 16
    rwa [← hs]

end OptimalOTS.RiscvMixedProgram
