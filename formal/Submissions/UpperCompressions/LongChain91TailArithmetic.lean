import Submissions.UpperCompressions.LongChain91BudgetArithmetic
import Submissions.UpperCompressions.LongChain91Occupancy

/-!
# Negligible completion tails for the cost-91 proof

The simultaneous occupancy exception is paid once.  The row-completion error
may be paid once per remaining signing opportunity.  Even at the largest
budget both fit together inside one `kappa * B / 1000` reserve.
-/

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91TailArithmetic

open ENNReal

abbrev kappa : ℝ := LongChain91BudgetArithmetic.kappa

theorem completion_exception_margin (B : ℝ) (hB : 1224 ≤ B)
    (hcap : B ≤ (2 : ℝ)^127) :
    ((2 : ℝ)^334)⁻¹ + (1 + B) * ((2 : ℝ)^760)⁻¹ ≤
      kappa * B / 1000 := by
  have hinv (n k : ℕ) (h : k ≤ n) :
      ((2 : ℝ)^n)⁻¹ ≤ ((2 : ℝ)^k)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) h
  have hocc := hinv 334 256 (by decide)
  have htab := hinv 760 384 (by decide)
  have hp : 0 ≤ 1 + B := by linarith
  have hb : 1 + B ≤ (2 : ℝ)^128 := by linarith
  have hterm := mul_le_mul htab hb hp
    (show (0 : ℝ) ≤ ((2 : ℝ)^384)⁻¹ by positivity)
  have he : ((2 : ℝ)^384)⁻¹ * (2 : ℝ)^128 =
      ((2 : ℝ)^256)⁻¹ := by
    rw [show (384 : ℕ) = 256 + 128 by omega, pow_add]
    field_simp
  rw [he, mul_comm _ (1 + B)] at hterm
  have hsmall : 2 * ((2 : ℝ)^256)⁻¹ ≤
      kappa * 1224 / 1000 := by
    norm_num [kappa, LongChain91BudgetArithmetic.kappa,
      Chain18Compact.kappa]
  have hfinal := mul_le_mul_of_nonneg_left hB
    (show 0 ≤ kappa / 1000 by
      exact div_nonneg LongChain91BudgetArithmetic.kappa_pos.le (by norm_num))
  have hbudget : kappa * 1224 / 1000 ≤ kappa * B / 1000 := by
    nlinarith
  calc
    _ ≤ ((2 : ℝ)^256)⁻¹ + ((2 : ℝ)^256)⁻¹ :=
      add_le_add hocc hterm
    _ = 2 * ((2 : ℝ)^256)⁻¹ := by ring
    _ ≤ kappa * 1224 / 1000 := hsmall
    _ ≤ kappa * B / 1000 := hbudget

theorem completion_exception_margin_ennreal (B : ℕ) (hB : 1224 ≤ B)
    (hcap : (B : ℝ) ≤ (2 : ℝ)^127) :
    (2 : ℝ≥0∞)⁻¹^334 +
        (1 + (B : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹^760 ≤
      ENNReal.ofReal (kappa * (B : ℝ) / 1000) := by
  have h := ENNReal.ofReal_le_ofReal
    (completion_exception_margin (B : ℝ) (by exact_mod_cast hB) hcap)
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)] at h
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_natCast,
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)^334),
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)^760),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, inv_pow] at h
  simpa only [ENNReal.inv_pow] using h

end OptimalOTS.WeightedConstruction.LongChain91TailArithmetic
