import Mathlib

/-!
The deterministic row inequality for a nonce space of size `2 * I`, where `I`
is the cut-class universe. This file proves only the real arithmetic step;
the adaptive-probability, transcript-padding and scheme-security arguments are
separate obligations.
-/

namespace TightIndex

/-- Main branch, written without a ratio so no positive-denominator premise is
needed. `A - v` counts repeated accepted entries, hence `b ≤ 2 * (A - v)`. -/
theorem row_main (I M p q L A v a b f : ℝ)
    (hI : 0 < I) (hM : 0 < M) (hp : p = M / I)
    (hv : 0 ≤ v) (hAv : v ≤ A) (hba : b ≤ a) (hb : 0 ≤ b)
    (hrep : b ≤ 2 * (A - v)) (hf : 2 * I - q - L ≤ f)
    (hT : max A (p * (q + L) / 2) < M) :
    M * (b + f * v / I) ≤ max A (p * (q + L) / 2) * (a + p * f) := by
  let T := max A (p * (q + L) / 2)
  have hTA : A ≤ T := le_max_left _ _
  have hTq : p * (q + L) / 2 ≤ T := le_max_right _ _
  have hTv : v ≤ T := hAv.trans hTA
  have hT0 : 0 ≤ T := hv.trans hTv
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hpI : p * I = M := by rw [hp]; exact div_mul_cancel₀ M hI.ne'
  have hgap : 2 * (M - T) ≤ p * f := by
    have hmul := mul_le_mul_of_nonneg_left hf hp0
    nlinarith
  have hMT : 0 ≤ M - T := by change T < M at hT; linarith
  have hbt : b ≤ 2 * (T - v) := by linarith
  have hfirst : M * b - T * a ≤ (M - T) * b := by
    have := mul_le_mul_of_nonneg_left hba hT0
    nlinarith
  have hsecond : (M - T) * b ≤ 2 * (M - T) * (T - v) := by
    have := mul_le_mul_of_nonneg_left hbt hMT
    nlinarith
  have hthird : 2 * (M - T) * (T - v) ≤ p * f * (T - v) := by
    exact mul_le_mul_of_nonneg_right hgap (sub_nonneg.mpr hTv)
  have hchain : M * b - T * a ≤ p * f * (T - v) :=
    hfirst.trans (hsecond.trans hthird)
  have heq : M * (b + f * v / I) = M * b + p * f * v := by
    rw [hp]
    ring
  change M * (b + f * v / I) ≤ T * (a + p * f)
  rw [heq]
  nlinarith

/-- Complete cross-multiplied inequality. The large-T branch uses `v ≤ M`,
`b ≤ a` and nonnegative fresh mass to bound bad mass by total accepting mass. -/
theorem row_bound (I M p q L A v a b f : ℝ)
    (hI : 0 < I) (hM : 0 < M) (hp : p = M / I)
    (hv : 0 ≤ v) (hvM : v ≤ M) (hAv : v ≤ A)
    (hba : b ≤ a) (hb : 0 ≤ b) (hrep : b ≤ 2 * (A - v))
    (hbudget : q + L ≤ 2 * I) (hf : 2 * I - q - L ≤ f) :
    M * (b + f * v / I) ≤ max A (p * (q + L) / 2) * (a + p * f) := by
  by_cases hT : max A (p * (q + L) / 2) < M
  · exact row_main I M p q L A v a b f hI hM hp hv hAv hba hb hrep hf hT
  · have hMT : M ≤ max A (p * (q + L) / 2) := le_of_not_gt hT
    have hf0 : 0 ≤ f := by linarith
    have ha0 : 0 ≤ a := hb.trans hba
    have hp0 : 0 ≤ p := by rw [hp]; positivity
    have hden : 0 ≤ a + p * f := by positivity
    have hvi : v / I ≤ p := by
      rw [hp]
      exact div_le_div_of_nonneg_right hvM hI.le
    have hbad : b + f * v / I ≤ a + p * f := by
      have hmul := mul_le_mul_of_nonneg_left hvi hf0
      rw [mul_div_assoc] at *
      nlinarith
    exact (mul_le_mul_of_nonneg_left hbad hM.le).trans
      (mul_le_mul_of_nonneg_right hMT hden)

#print axioms row_main
#print axioms row_bound

end TightIndex
