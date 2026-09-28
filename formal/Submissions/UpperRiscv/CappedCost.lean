import Submissions.UpperRiscv.Valid

/-! Arithmetic envelope for every path through the free chain and the capped pairs. -/
namespace OptimalOTS.CappedCost

/-- Cycles of a passing pair besides its digit hashes. -/
def overhead (q : ℕ) : ℕ := [10,10,8,9,9,8,9,9,8,9,9,8,8,8,8,7].getD q 0

/-- Cycles of a pair whose landing rejects. -/
def rejectCost (q : ℕ) : ℕ := [10,10,8,10,8,8,10,8,8,10,9,8,8,8,8,8].getD q 0

/-- Pairs from `q` on, then the root (at most 13 blocks) and the decision. -/
def cost (w : ℕ → ℕ) : (n q : ℕ) → ℕ
  | 0, _ => 21
  | n+1, q => if w q ≤ PairCode.cap q then
      overhead q + w q + cost w n (q+1)
    else rejectCost q

set_option maxHeartbeats 4000000 in
/-- The free chain (`6 + v` cycles) and the pairs: either all sixteen pairs pass with digit sum
`146 - v`, or the first bad pair stops early. The alias `S + v = 401` cannot pass all caps. -/
theorem bound (w : ℕ → ℕ) (hw : ∀ q < 16, w q ≤ 30) (v : ℕ) (hv : v < 16)
    (check : ((∑ q ∈ Finset.range 16, w q) + v) % 255 = 146) :
    6 + v + cost w 16 0 ≤ 310 := by
  have h10 := hw 10 (by omega)
  have h11 := hw 11 (by omega)
  have h12 := hw 12 (by omega)
  have h13 := hw 13 (by omega)
  have h14 := hw 14 (by omega)
  have h15 := hw 15 (by omega)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd] at check
  norm_num [cost, overhead, rejectCost, PairCode.cap]
  repeat' first | omega | split

end OptimalOTS.CappedCost
