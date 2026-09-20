import Mathlib

/-!
Pure real inequalities for the tighter index-cache potential.
If a fresh accepted indicator is Bernoulli p, the walk D increases by
p/2 minus that indicator. Its exponential has nonpositive drift.
This file does not yet prove a theorem about the oracle computation.
-/

namespace TightIndex

theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr h

theorem exp_drift (p d : ℝ) (hp : 0 ≤ p) :
    (1 - p) * Real.exp (d + p / 2) + p * Real.exp (d + p / 2 - 1)
      ≤ Real.exp d := by
  have h1 : 1 - p + p * Real.exp (-1) ≤ 1 - p / 2 := by
    have := mul_le_mul_of_nonneg_left exp_neg_one_le_half hp
    linarith
  have h2 : 1 - p / 2 ≤ Real.exp (-(p / 2)) := by
    linarith [Real.add_one_le_exp (-(p / 2))]
  have heq : (1 - p) * Real.exp (d + p / 2) + p * Real.exp (d + p / 2 - 1) =
      Real.exp (d + p / 2) * (1 - p + p * Real.exp (-1)) := by
    have he : Real.exp (d + p / 2 - 1) = Real.exp (d + p / 2) * Real.exp (-1) := by
      simpa only [sub_eq_add_neg] using Real.exp_add (d + p / 2) (-1)
    rw [he]
    ring
  rw [heq]
  calc
    _ ≤ Real.exp (d + p / 2) * Real.exp (-(p / 2)) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
    _ = Real.exp d := by rw [← Real.exp_add]; congr 1; ring

theorem positive_part_le_exp (d : ℝ) : max d 0 ≤ Real.exp d := by
  apply max_le
  · linarith [Real.add_one_le_exp d]
  · exact (Real.exp_pos d).le

/-- Pointwise conversion of the row cap to accepted-count and exponential terms. -/
theorem row_cap_le_exp (p q L A : ℝ) (hpL : 0 ≤ p * L) :
    max A (p * (q + L) / 2) ≤
      A + p * L / 2 + Real.exp (p * q / 2 - A)
    := by
  have hpos := positive_part_le_exp (p * q / 2 - A)
  have hm : max A (p * (q + L) / 2) ≤
      A + p * L / 2 + max (p * q / 2 - A) 0 := by
    apply max_le
    · linarith [le_max_right (p * q / 2 - A) 0]
    · nlinarith [le_max_left (p * q / 2 - A) 0]
  linarith

noncomputable def cachePotential (p M L A q : ℝ) : ℝ :=
  (A + p * L / 2 + Real.exp (p * q / 2 - A)) / M

theorem cachePotential_nonneg (p M L A q : ℝ)
    (hA : 0 ≤ A) (hpL : 0 ≤ p * L) (hM : 0 ≤ M) :
    0 ≤ cachePotential p M L A q := by
  unfold cachePotential
  apply div_nonneg _ hM
  linarith [Real.exp_pos (p * q / 2 - A)]

/-- Expected charge of one fresh encoding answer; accepted with probability p. -/
theorem cachePotential_step (p M L A q : ℝ) (hp : 0 ≤ p) (hM : 0 < M) :
    (1 - p) * cachePotential p M L A (q + 1) +
      p * cachePotential p M L (A + 1) (q + 1) ≤
        cachePotential p M L A q + p / M := by
  have h := exp_drift p (p * q / 2 - A) hp
  have e1 : p * q / 2 - A + p / 2 = p * (q + 1) / 2 - A := by ring
  have e2 : p * q / 2 - A + p / 2 - 1 = p * (q + 1) / 2 - (A + 1) := by ring
  rw [e2, e1] at h
  have hh := div_le_div_of_nonneg_right
    (add_le_add_left h (A + p * L / 2 + p)) hM.le
  calc
    _ = (A + p * L / 2 + p + ((1 - p) * Real.exp (p * (q + 1) / 2 - A) +
        p * Real.exp (p * (q + 1) / 2 - (A + 1)))) / M := by
      unfold cachePotential
      ring
    _ ≤ (A + p * L / 2 + p + Real.exp (p * q / 2 - A)) / M := by
      simpa only [add_comm] using hh
    _ = _ := by unfold cachePotential; ring

theorem cachePotential_zero (I M p L : ℝ) (hI : I ≠ 0) (hM : M ≠ 0)
    (hp : p = M / I) :
    cachePotential p M L 0 0 = L / (2 * I) + 1 / M := by
  simp only [cachePotential, mul_zero, zero_div, sub_zero, Real.exp_zero, zero_add]
  rw [hp]
  field_simp

/-- The positive initial potential fits strictly inside the reserved signing budget. -/
theorem initial_slack (I M p L : ℝ) (hI : 0 < I) (hM : 0 < M)
    (hp : p = M / I) (hwork : 2 < p * L) :
    L / (2 * I) + 1 / M < L / I := by
  have hpI : p * I = M := by rw [hp]; exact div_mul_cancel₀ M hI.ne'
  have hwork' : 2 * I < M * L := by
    have := mul_lt_mul_of_pos_right hwork hI
    nlinarith
  apply (sub_pos).mp
  have he : L / I - (L / (2 * I) + 1 / M) = (M * L - 2 * I) / (2 * I * M) := by
    field_simp
    ring
  rw [he]
  exact div_pos (by linarith) (by positivity)

#print axioms exp_drift
#print axioms positive_part_le_exp
#print axioms row_cap_le_exp
#print axioms cachePotential_step
#print axioms cachePotential_zero
#print axioms initial_slack

end TightIndex
