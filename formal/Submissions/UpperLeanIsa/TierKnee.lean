import Submissions.UpperLeanIsa.TierNumeric

/-! The largest integer knee allowed by the schedule's linear budget condition.
This is a research helper; the certified 1124 schedule still uses knee one. -/

namespace OptimalOTS.LeanIsaBaseline.Layer.Tier.Knee

/-- Continuous limit on `b0 - 1` when the collision slope is positive. -/
def cap (hp k1 : ℚ) : ℚ := 2 ^ 128 * (2 * k1 - hp) / hp

/-- An integer knee that uses all the available linear slack. -/
def chosen (hp k1 : ℚ) : ℕ := ⌊cap hp k1⌋₊ + 1

theorem chosen_pos (hp k1 : ℚ) : 1 ≤ chosen hp k1 := by
  unfold chosen
  omega

theorem cap_nonneg {hp k1 : ℚ} (hh : 0 < hp) (hk : hp ≤ 2 * k1) :
    0 ≤ cap hp k1 := by
  unfold cap
  exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hk)) hh.le

theorem chosen_legal {hp k1 : ℚ} (hh : 0 < hp) (hk : hp ≤ 2 * k1) :
    hp * ((chosen hp k1 : ℚ) - 1) ≤ 2 ^ 128 * (2 * k1 - hp) := by
  have hf := Nat.floor_le (cap_nonneg hh hk)
  have hm := mul_le_mul_of_nonneg_left hf hh.le
  have he : hp * cap hp k1 = 2 ^ 128 * (2 * k1 - hp) := by
    unfold cap
    field_simp
  simpa [chosen, Nat.cast_add, Nat.cast_one, he] using hm

/-- Any legal positive knee is at most the chosen one. -/
theorem maximal {hp k1 : ℚ} (hh : 0 < hp) {b : ℕ}
    (hb : hp * ((b : ℚ) - 1) ≤ 2 ^ 128 * (2 * k1 - hp)) :
    b ≤ chosen hp k1 := by
  have hb' : (b : ℚ) - 1 ≤ cap hp k1 := by
    unfold cap
    apply (le_div_iff₀ hh).2
    simpa [mul_comm] using hb
  have hf := Nat.lt_floor_add_one (cap hp k1)
  have : (b : ℚ) < (chosen hp k1 : ℚ) + 1 := by
    simp only [chosen, Nat.cast_add, Nat.cast_one]
    linarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- Using the chosen knee never increases the quadratic budget term. -/
theorem improves {hp k1 : ℚ} (hh : 0 < hp) {b B : ℕ}
    (hb : hp * ((b : ℚ) - 1) ≤ 2 ^ 128 * (2 * k1 - hp)) :
    hp / (4 * 2 ^ 128) * ((B - chosen hp k1 : ℕ) : ℚ) ^ 2 ≤
      hp / (4 * 2 ^ 128) * ((B - b : ℕ) : ℚ) ^ 2 := by
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Nat.sub_le_sub_left (maximal hh hb) B
  · positivity

/-- Rounded integer subtraction is bounded by the continuous positive part. -/
theorem tail_le (hp k1 : ℚ) (B : ℕ) :
    ((B - chosen hp k1 : ℕ) : ℚ) ≤ max 0 ((B : ℚ) - cap hp k1) := by
  by_cases hb : chosen hp k1 ≤ B
  · rw [Nat.cast_sub hb]
    apply le_trans _ (le_max_right _ _)
    have hf := Nat.lt_floor_add_one (cap hp k1)
    simp only [chosen, Nat.cast_add, Nat.cast_one]
    linarith
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hb)), Nat.cast_zero]
    exact le_max_left _ _

end OptimalOTS.LeanIsaBaseline.Layer.Tier.Knee
