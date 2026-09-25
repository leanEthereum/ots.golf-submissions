import Submissions.UpperRiscvHint.Valid

/-! Arithmetic envelope for every path through the capped-pair verifier. -/
namespace OptimalOTS.CappedCost

def overhead (q : ℕ) : ℕ :=
  8 + (if q = 0 ∨ q = 1 then 2 else if q = 2 ∨ q = 4 ∨ q = 5 ∨ q = 7 then 1 else 0) +
    (if q = 8 then 1 else 0)

def rejectCost (q : ℕ) : ℕ :=
  8 + (if q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 7 then 2 else 0) + (if q = 8 then 1 else 0)

def cost (w : ℕ → ℕ) : (n q : ℕ) → ℕ
  | 0, _ => 21
  | n+1, q => if w q ≤ PairCode.cap q then
      overhead q + w q + cost w n (q+1)
    else rejectCost q

set_option maxHeartbeats 2000000 in
/-- Either all sixteen pairs pass at rank 158, or the first bad pair stops
early. Rank 413 cannot pass all caps, whose sum is only 412. -/
theorem bound (w : ℕ → ℕ) (hw : ∀ q < 16, w q ≤ 30)
    (rank : (∑ q ∈ Finset.range 16, w q) = 158 ∨
            (∑ q ∈ Finset.range 16, w q) = 413) :
    cost w 16 0 ≤ 316 := by
  have h10 := hw 10 (by omega)
  have h11 := hw 11 (by omega)
  have h12 := hw 12 (by omega)
  have h13 := hw 13 (by omega)
  have h14 := hw 14 (by omega)
  have h15 := hw 15 (by omega)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd] at rank
  norm_num [cost, overhead, rejectCost, PairCode.cap]
  repeat' first | omega | split

end OptimalOTS.CappedCost
