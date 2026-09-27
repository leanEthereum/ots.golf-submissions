import Submissions.UpperRiscvHint.Valid

/-! Arithmetic of the capped-pair verifier's cycles after the free chain. -/
namespace OptimalOTS.CappedCost

/-- Per-pair cycles besides one hash per digit unit: the length setup before pair 6, the prologue,
the pointer move, and the extra hash of each normal chain. -/
def overhead (q : ℕ) : ℕ := (if q < 6 then 6 else 8) + if q = 6 then 1 else 0

def rejectCost (q : ℕ) : ℕ := 8 + if q = 6 then 1 else 0

def cost (w : ℕ → ℕ) : (n q : ℕ) → ℕ
  | 0, _ => 21
  | n+1, q => if w q ≤ PairCode.cap q then
      overhead q + w q + cost w n (q+1)
    else rejectCost q

/-- Every path fits in 33 cycles per pair plus the root and the decision. -/
theorem cost_le (w : ℕ → ℕ) : ∀ n q, cost w n q ≤ 33 * n + 21 := by
  intro n
  induction n with
  | zero => intro q; simp [cost]
  | succ n ih =>
    intro q
    have h := ih (q+1)
    rw [cost]
    split_ifs with hw
    · unfold overhead; unfold PairCode.cap at hw; split_ifs <;> omega
    · unfold rejectCost; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
/-- When all sixteen pairs pass, the pairs, the root and the decision cost 138 cycles besides the
digit sum. -/
theorem cost_allowed (w : ℕ → ℕ) (hw : ∀ q < 16, w q ≤ PairCode.cap q) :
    cost w 16 0 = 138 + ∑ q ∈ Finset.range 16, w q := by
  have h0 := hw 0 (by omega); have h1 := hw 1 (by omega); have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega); have h4 := hw 4 (by omega); have h5 := hw 5 (by omega)
  have h6 := hw 6 (by omega); have h7 := hw 7 (by omega); have h8 := hw 8 (by omega)
  have h9 := hw 9 (by omega); have h10 := hw 10 (by omega); have h11 := hw 11 (by omega)
  have h12 := hw 12 (by omega); have h13 := hw 13 (by omega); have h14 := hw 14 (by omega)
  have h15 := hw 15 (by omega)
  simp only [cost, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    if_true, overhead, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  omega

end OptimalOTS.CappedCost
