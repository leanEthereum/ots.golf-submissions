import Mathlib

/-!
# Mixed-width digits (ported from UpperRiscv `Digits.lean`)

For a width function `w`, `posW w k = w 0 + ⋯ + w (k-1)` is the bit position of digit `k`, and
`digitW w i k` reads the `w k` bits of `i` from that position. `ofDigitsW w c n` packs the digits
`c 0, …, c (n-1)`; the two are inverse to each other on the range `2 ^ posW w n`.
-/

namespace OptimalOTS.LeanIsaBaseline.Layer
variable (w : ℕ → ℕ)

/-- Position of digit `k`. -/
def posW : ℕ → ℕ
  | 0 => 0
  | k + 1 => posW k + w k

theorem posW_zero : posW w 0 = 0 := rfl

theorem posW_succ (k : ℕ) : posW w (k + 1) = posW w k + w k := rfl

theorem posW_add_le {j k : ℕ} (h : j < k) : posW w j + w j ≤ posW w k := by
  rw [← posW_succ]
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact (ih h').trans (by rw [posW_succ]; omega)
    · rw [h']

theorem two_pow_posW_dvd {j k : ℕ} (h : j < k) : 2 ^ (posW w j + w j) ∣ 2 ^ posW w k :=
  Nat.pow_dvd_pow 2 (posW_add_le w h)

/-- Digit `k` of `i`. -/
def digitW (i k : ℕ) : ℕ := i / 2 ^ posW w k % 2 ^ w k

theorem digitW_lt (i k : ℕ) : digitW w i k < 2 ^ w k := Nat.mod_lt _ (by positivity)

/-- The number whose `n` low digits are `c 0, …, c (n - 1)`. -/
def ofDigitsW (c : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, c k * 2 ^ posW w k

theorem ofDigitsW_zero (c : ℕ → ℕ) : ofDigitsW w c 0 = 0 := by simp [ofDigitsW]

theorem ofDigitsW_succ (c : ℕ → ℕ) (n : ℕ) :
    ofDigitsW w c (n + 1) = ofDigitsW w c n + c n * 2 ^ posW w n := by
  unfold ofDigitsW
  rw [Finset.sum_range_succ]

theorem ofDigitsW_lt (c : ℕ → ℕ) (hc : ∀ k, c k < 2 ^ w k) :
    ∀ n, ofDigitsW w c n < 2 ^ posW w n := by
  intro n
  induction n with
  | zero => simp [ofDigitsW_zero, posW_zero]
  | succ n ih =>
    rw [ofDigitsW_succ, posW_succ, pow_add]
    have hc' : c n + 1 ≤ 2 ^ w n := hc n
    calc ofDigitsW w c n + c n * 2 ^ posW w n < 2 ^ posW w n + c n * 2 ^ posW w n := by omega
      _ = (c n + 1) * 2 ^ posW w n := by ring
      _ ≤ 2 ^ w n * 2 ^ posW w n := Nat.mul_le_mul_right _ hc'
      _ = 2 ^ posW w n * 2 ^ w n := mul_comm _ _

/-- Adding a multiple of `2 ^ posW w n` does not change the digits below `n`. -/
theorem digitW_add_mul {i q j n : ℕ} (hj : j < n) :
    digitW w (i + q * 2 ^ posW w n) j = digitW w i j := by
  unfold digitW
  obtain ⟨r, hr⟩ := two_pow_posW_dvd w hj
  rw [hr, pow_add,
    show q * (2 ^ posW w j * 2 ^ w j * r) = (q * 2 ^ w j * r) * 2 ^ posW w j by ring,
    Nat.add_mul_div_right _ _ (by positivity),
    show q * 2 ^ w j * r = (q * r) * 2 ^ w j by ring, Nat.add_mul_mod_self_right]

theorem digitW_ofDigitsW (c : ℕ → ℕ) (hc : ∀ k, c k < 2 ^ w k) :
    ∀ n j, j < n → digitW w (ofDigitsW w c n) j = c j := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rw [ofDigitsW_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · rw [digitW_add_mul w h, ih j h]
    · subst h
      unfold digitW
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (ofDigitsW_lt w c hc j),
        zero_add, Nat.mod_eq_of_lt (hc j)]

theorem digitW_mod {i j n : ℕ} (hj : j < n) : digitW w (i % 2 ^ posW w n) j = digitW w i j := by
  conv_rhs => rw [← Nat.mod_add_div i (2 ^ posW w n)]
  rw [mul_comm, digitW_add_mul w hj]

theorem ofDigitsW_digitW (i : ℕ) : ∀ n, i < 2 ^ posW w n → ofDigitsW w (digitW w i) n = i := by
  intro n
  induction n generalizing i with
  | zero => intro hi; rw [ofDigitsW_zero]; rw [posW_zero] at hi; omega
  | succ n ih =>
    intro hi
    rw [ofDigitsW_succ]
    have hmod : ofDigitsW w (digitW w i) n = ofDigitsW w (digitW w (i % 2 ^ posW w n)) n := by
      unfold ofDigitsW
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [digitW_mod w (Finset.mem_range.mp hj)]
    rw [hmod, ih _ (Nat.mod_lt _ (by positivity))]
    have hq : i / 2 ^ posW w n < 2 ^ w n := by
      rw [posW_succ, pow_add] at hi
      exact Nat.div_lt_of_lt_mul hi
    unfold digitW
    rw [Nat.mod_eq_of_lt hq, mul_comm]
    exact Nat.mod_add_div i (2 ^ posW w n)

theorem posW_mono {n k : ℕ} (hk : n ≤ k) : posW w n ≤ posW w k := by
  induction k with
  | zero => rw [Nat.le_zero.mp hk]
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with h | h
    · exact (ih (by omega)).trans (by rw [posW_succ]; omega)
    · rw [h]

/-- Digits of a number below `2 ^ posW w n` vanish from `n` on. -/
theorem digitW_eq_zero_of_lt {i n k : ℕ} (hi : i < 2 ^ posW w n) (hk : n ≤ k) :
    digitW w i k = 0 := by
  unfold digitW
  have : i < 2 ^ posW w k :=
    lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (posW_mono w hk))
  rw [Nat.div_eq_of_lt this, Nat.zero_mod]

end OptimalOTS.LeanIsaBaseline.Layer
