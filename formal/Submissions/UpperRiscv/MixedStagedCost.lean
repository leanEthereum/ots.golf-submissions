import Submissions.UpperRiscv.MixedPair
import Submissions.UpperRiscv.CappedCost

namespace OptimalOTS.RiscvMixedProgram

def pairWeight (index : RawIdx) (q : ℕ) : ℕ :=
  digit index.val (2*q) + digit index.val (2*q+1)

theorem overhead_eq' : ∀ q : Fin 16,
    (lengthSetup q).length + 8 + 2*earlyHash (leftChain q) + 2*earlyHash (rightChain q) =
      CappedCost.overhead q.val + rowShort (leftChain q) + rowShort (rightChain q) := by
  decide +kernel

theorem rowShort_le' : ∀ k : Fin 33, rowShort k ≤ 1 := by decide +kernel

theorem pairCost_overhead (index : RawIdx) (v : ℕ) (hv : v < 16) (q : Fin 16) :
    pairCost index v q = CappedCost.overhead q.val + pairWeight index q.val := by
  have h := overhead_eq' q
  have ra := rowShort_le' (leftChain q)
  have rb := rowShort_le' (rightChain q)
  rw [pairCost_eq index v q hv]
  unfold pairWeight coarseDigit
  omega

theorem badPairCost_eq (q : Fin 16) : badPairCost q = CappedCost.rejectCost q.val := by
  revert q
  decide +kernel

theorem stagedCost_eq (index : RawIdx) (v : ℕ) (hv : v < 16) (n q : ℕ) (hq : q+n ≤ 16) :
    stagedCost index v n q = CappedCost.cost (pairWeight index) n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [stagedCost, dif_pos (show q < 16 by omega), CappedCost.cost]
    change (if pairWeight index q ≤ PairCode.cap q then
      pairCost index v ⟨q, by omega⟩ + stagedCost index v n (q+1) else badPairCost ⟨q, by omega⟩) = _
    split_ifs
    · rw [pairCost_overhead index v hv, ih (q+1) (by omega)]
    · exact badPairCost_eq _

/-- The free chain, every pair path and the root fit in 310 cycles. -/
theorem stagedCost_le (index : RawIdx) (v : ℕ) (hv : v < 16)
    (check : (digitSum index.val + v) % 255 = 146) :
    6 + v + stagedCost index v 16 0 ≤ 310 := by
  rw [stagedCost_eq index v hv 16 0 (by decide)]
  refine CappedCost.bound _ ?_ v hv ?_
  · intro q _
    have ha := digit_lt_16 index.val (2*q)
    have hb := digit_lt_16 index.val (2*q+1)
    unfold pairWeight
    omega
  · have hs : digitSum index.val = ∑ q ∈ Finset.range 16, pairWeight index q := by
      unfold digitSum pairWeight
      exact digit_sum_pairs index.val
    have h := check
    rw [hs] at h
    exact h

end OptimalOTS.RiscvMixedProgram
