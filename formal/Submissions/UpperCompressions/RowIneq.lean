import Mathlib

/-!
# The arithmetic of one encoding query

`charge_le`: the expected increase of the row potential under one fresh encoding query, in units of
`2 ^ -idxBits`, is at most `11/6`. The variables describe the queried row after the reduction of the
other rows to the row budget (see `docs/nonce-128-analysis.md`): `w = q N₀ ∈ [M/2, M]` with
`q = M / I`, `D₀ = a₀ + w`, `x₀⁺ ≤ (1 − r) a₀`, `d₀ ≤ a₀`, and `S` the other rows' collision term.
-/

namespace OptimalOTS.RowIneq

/-- The two-variable core: `y = w / D₀ ∈ (0, 1]`, `ω = w / M ∈ [1/2, 1]`. -/
theorem core (y ω : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hω0 : 1/2 ≤ ω) (hω1 : ω ≤ 1) :
    y * (1 - y/2)^2 ≤ ω/3 + ω*(1-ω)*y := by
  nlinarith [mul_nonneg hy0 (sub_nonneg.2 hy1), mul_nonneg (sub_nonneg.2 hω0) (sub_nonneg.2 hω1),
    mul_nonneg (mul_nonneg hy0 (sub_nonneg.2 hy1)) (sub_nonneg.2 hω0),
    mul_nonneg (mul_nonneg hy0 hy0) (sub_nonneg.2 hω0), sq_nonneg (y - 1/2), sq_nonneg (y - 2/3),
    mul_nonneg hy0 (sub_nonneg.2 hω0), mul_nonneg hy0 (sub_nonneg.2 hω1),
    mul_nonneg (mul_nonneg hy0 (sub_nonneg.2 hy1)) (sub_nonneg.2 hω1)]

/-- The queried row: `M (2 D₀ − w)² / (4 D₀³) − (M − w) w / (M D₀) ≤ 1/3`. -/
theorem row (M w D : ℝ) (hM : 0 < M) (hw1 : M / 2 ≤ w) (hw2 : w ≤ M) (hD : w ≤ D) :
    M * (2 * D - w)^2 / (4 * D^3) - (M - w) * w / (M * D) ≤ 1/3 := by
  have hw0 : 0 < w := by linarith
  have hD0 : 0 < D := by linarith
  set y := w / D with hy
  set ω := w / M with hω
  have hy0 : 0 ≤ y := div_nonneg hw0.le hD0.le
  have hy1 : y ≤ 1 := (div_le_one hD0).2 hD
  have hω0 : 1/2 ≤ ω := by rw [hω, le_div_iff₀ hM]; linarith
  have hω1 : ω ≤ 1 := (div_le_one hM).2 hw2
  have hc := core y ω hy0 hy1 hω0 hω1
  have e1 : M * (2 * D - w)^2 / (4 * D^3) = (y / ω) * (1 - y/2)^2 := by
    rw [hy, hω]; field_simp; ring
  have e2 : (M - w) * w / (M * D) = (1 - ω) * y := by
    rw [hy, hω]; field_simp
  rw [e1, e2]
  have hωp : 0 < ω := by linarith
  rw [div_mul_eq_mul_div, div_sub' hωp.ne', div_le_iff₀ hωp]
  nlinarith [hc]

/-- **The charge of one encoding query**, in units of `2 ^ -idxBits`. -/
theorem charge_le (M I a0 d0 w x0p r S : ℝ) (hM : 0 < M) (hMI : M ≤ I)
    (hw1 : M / 2 ≤ w) (hw2 : w ≤ M) (ha0 : 0 ≤ a0) (hd0 : 0 ≤ d0) (hd0a : d0 ≤ a0)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx0 : 0 ≤ x0p) (hx1 : x0p ≤ (1 - r) * a0)
    (hD1 : 1 ≤ a0 + w) (hMI2 : 2 * M ≤ I)
    (hS : S ≤ r - d0 / M + 1/2 - (M - w) / M) :
    (I - M) * (x0p / (a0 + w - M / I) - x0p / (a0 + w)) + (1 - r) +
      (r * M * (1 - r) + d0) / (a0 + w) + S ≤ 11/6 := by
  have hI : 0 < I := lt_of_lt_of_le hM hMI
  have hq0 : 0 ≤ M / I := div_nonneg hM.le hI.le
  have hq1 : M / I ≤ 1 := (div_le_one hI).2 hMI
  set D := a0 + w with hD
  have hDpos : 0 < D := by linarith
  have hDq : 0 < D - M / I := by
    have : M / I ≤ 1 / 2 := by rw [div_le_iff₀ hI]; linarith
    linarith
  -- step A: the invalid-answer drift
  have hA : (I - M) * (x0p / (D - M / I) - x0p / D) ≤ M * x0p / D^2 := by
    have e : x0p / (D - M / I) - x0p / D = x0p * (M / I) / (D * (D - M / I)) := by
      rw [div_sub_div _ _ hDq.ne' hDpos.ne']; ring
    rw [e]
    have hIM : (I - M) * (M / I) = M * (1 - M / I) := by field_simp
    rw [show (I - M) * (x0p * (M / I) / (D * (D - M / I))) =
        x0p * ((I - M) * (M / I)) / (D * (D - M / I)) by ring, hIM]
    rw [div_le_div_iff₀ (mul_pos hDpos hDq) (by positivity)]
    have : (1 - M / I) * D ≤ D - M / I := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hx0 hM.le) hDpos.le, mul_le_mul_of_nonneg_left this
      (mul_nonneg (mul_nonneg hx0 hM.le) hDpos.le)]
  -- step B: the queried row's own collisions against the row budget
  have hB : (d0 / D) - d0 / M - (M - w) / M ≤ -((M - w) * w / (M * D)) := by
    have key : d0 / D - d0 / M - (M - w) / M + (M - w) * w / (M * D) =
        ((M - w) * (w - D) + d0 * (M - D)) / (M * D) := by
      field_simp; ring
    have hneg : ((M - w) * (w - D) + d0 * (M - D)) / (M * D) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith [mul_nonneg (sub_nonneg.2 hw2) ha0, mul_nonneg hd0 ha0]
    linarith
  -- step C: the index-guess and drift terms
  have hC : r * M * (1 - r) / D + M * x0p / D^2 ≤ M * (2 * D - w)^2 / (4 * D^3) := by
    have h1 : M * x0p / D^2 ≤ M * ((1 - r) * a0) / D^2 := by gcongr
    have h2 : r * M * (1 - r) / D + M * ((1 - r) * a0) / D^2 =
        M * ((1 - r) * D * (r * D + a0)) / D^3 := by field_simp
    have h3 : 4 * ((1 - r) * D * (r * D + a0)) ≤ (2 * D - w)^2 := by
      nlinarith [sq_nonneg ((1 - r) * D - (r * D + a0))]
    calc r * M * (1 - r) / D + M * x0p / D^2 ≤ r * M * (1 - r) / D + M * ((1 - r) * a0) / D^2 := by
          linarith
      _ = M * ((1 - r) * D * (r * D + a0)) / D^3 := h2
      _ ≤ M * ((2 * D - w)^2 / 4) / D^3 := by gcongr; linarith
      _ = M * (2 * D - w)^2 / (4 * D^3) := by field_simp
  have hRow := row M w D hM hw1 hw2 (by linarith)
  have e3 : (r * M * (1 - r) + d0) / D = r * M * (1 - r) / D + d0 / D := by ring
  rw [e3]
  linarith [hA, hB, hC, hRow, hS]

end OptimalOTS.RowIneq
