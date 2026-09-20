import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace AvailabilityCubic

attribute [local irreducible] Nat.choose

lemma cubic_binomial_lower (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 3 ≤ n) :
    1 + (n : ℝ) * x + (n.choose 2 : ℝ) * x ^ 2 + (n.choose 3 : ℝ) * x ^ 3 ≤
      (1 + x) ^ n := by
  have hs : Finset.range 4 ⊆ Finset.range (n + 1) := by
    apply Finset.range_mono
    omega
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i =>
    x ^ i * (1 : ℝ) ^ (n - i) * (n.choose i : ℝ)) hs (by
      intro i hi hni
      positivity)
  rw [← add_pow] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_pow,
    mul_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    zero_add, pow_one] at h
  simpa only [add_comm, add_left_comm, add_assoc, mul_comm] using h

lemma choose_two : Nat.choose 8192 2 = 33550336 := by
  rw [Nat.choose_two_right]

lemma choose_three : Nat.choose 8192 3 = 91592417280 := by
  have h := Nat.choose_succ_right_eq 8192 2
  norm_num [choose_two] at h
  omega

lemma reciprocal_power_lower :
    (2 : ℝ) ≤ (1 + 45 / 524243) ^ 8192 := by
  have h := cubic_binomial_lower (45 / 524243) (by norm_num) 8192 (by norm_num)
  rw [choose_two, choose_three] at h
  have hc : (2 : ℝ) ≤ 1 + (8192 : ℝ) * (45 / 524243) +
      (33550336 : ℝ) * (45 / 524243) ^ 2 +
      (91592417280 : ℝ) * (45 / 524243) ^ 3 := by norm_num
  exact hc.trans h

/-- An 8192-trial block fails with probability at most one half. -/
theorem block_bound : (1 - (45 : ℝ) / 524288) ^ 8192 ≤ 1 / 2 := by
  have hn : 0 ≤ (1 - (45 : ℝ) / 524288) ^ 8192 := by positivity
  have hp : (1 - (45 : ℝ) / 524288) ^ 8192 *
      (1 + 45 / 524243) ^ 8192 = 1 := by
    have hbase : (1 - (45 : ℝ) / 524288) * (1 + 45 / 524243) = 1 := by norm_num
    rw [← mul_pow, hbase, one_pow]
  have h := mul_le_mul_of_nonneg_left reciprocal_power_lower hn
  rw [hp] at h
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 h

/-- The numerical failure bound for 2^20 fresh independent index trials. -/
theorem signing_failure_bound :
    (1 - (45 : ℝ) / 524288) ^ (2 ^ 20 : ℕ) ≤ ((2 : ℝ) ^ 128)⁻¹ := by
  have he : (2 ^ 20 : ℕ) = 8192 * 128 := by norm_num
  rw [he, pow_mul]
  calc
    ((1 - (45 : ℝ) / 524288) ^ 8192) ^ 128 ≤ ((1 : ℝ) / 2) ^ 128 :=
      pow_le_pow_left₀ (by positivity) block_bound 128
    _ = ((2 : ℝ) ^ 128)⁻¹ := by rw [one_div, inv_pow]

#print axioms block_bound
#print axioms signing_failure_bound
end AvailabilityCubic
