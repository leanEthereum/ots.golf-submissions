import Submissions.UpperLeanIsa.TierNumeric

/-!
# The numeric kernel of rarest-cut signing in `ℝ≥0∞`

The tier schedule's quantities cast to `ℝ≥0∞` (`yb`, `pE`, `fE`, `k1E`, `hpE`), the finite
geometric sums `gsum`/`sck` of the per-row potential with their recursions `winA`/`scB`, the budget
`Kb b = κ₁ b + H' / (4 I) ((b - b0)⁺) ^ 2`, and the bounds that `Sched.Valid` gives on them.
-/

noncomputable section

open scoped ENNReal

namespace OptimalOTS.LeanIsaBaseline.Layer.Tier

/-- `Σ_{j<k} x ^ j y ^ (k - 1 - j)`, so that `(y - x) gsum = y ^ k - x ^ k`. -/
def gsum (x y : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ := ∑ j ∈ Finset.range k, x ^ j * y ^ (k - 1 - j)

/-- `Σ_{j<k} (k - 1 - j) x ^ j y ^ (k - 2 - j)`, the `y`-derivative of `gsum`. -/
def sck (x y : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range k, ((k - 1 - j : ℕ) : ℝ≥0∞) * (x ^ j * y ^ (k - 2 - j))

/-- The recursion `A_{k+1} = q y ^ k + x A_k` of the win probability over `k` trials. -/
def winA (x y q : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | k + 1 => q * y ^ k + x * winA x y q k

/-- The recursion `B_{k+1} = q k r y ^ (k - 1) + x B_k` of the second-order correction. -/
def scB (x y q r : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | k + 1 => q * ((k : ℝ≥0∞) * r * y ^ (k - 1)) + x * scB x y q r k

/-- the row factor I/(I-L) -/
def cIE : ℝ≥0∞ := 2 ^ 127 / (2 ^ 127 - 2 ^ 19)

theorem gsum_succ (x y : ℝ≥0∞) (k : ℕ) : gsum x y (k + 1) = y ^ k + x * gsum x y k := by
  unfold gsum
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show k + 1 - 1 - (j + 1) = k - 1 - j by omega, pow_succ]
    ring

theorem gsum_succ' (x y : ℝ≥0∞) (k : ℕ) : gsum x y (k + 1) = x ^ k + y * gsum x y k := by
  unfold gsum
  rw [Finset.sum_range_succ, Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    rw [show k + 1 - 1 - j = (k - 1 - j) + 1 by omega, pow_succ]
    ring

theorem sck_succ (x y : ℝ≥0∞) (k : ℕ) :
    sck x y (k + 1) = (k : ℝ≥0∞) * y ^ (k - 1) + x * sck x y k := by
  unfold sck
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show k + 1 - 1 - (j + 1) = k - 1 - j by omega,
      show k + 1 - 2 - (j + 1) = k - 2 - j by omega, pow_succ]
    ring

theorem winA_eq (x y q : ℝ≥0∞) (k : ℕ) : winA x y q k = q * gsum x y k := by
  induction k with
  | zero => simp [winA, gsum]
  | succ k ih => rw [winA, ih, gsum_succ]; ring

theorem scB_eq (x y q r : ℝ≥0∞) (k : ℕ) : scB x y q r k = q * r * sck x y k := by
  induction k with
  | zero => simp [scB, sck]
  | succ k ih => rw [scB, ih, sck_succ]; ring

theorem y_mul_sck_le (x y : ℝ≥0∞) (k : ℕ) :
    y * sck x y k ≤ ((k - 1 : ℕ) : ℝ≥0∞) * gsum x y k := by
  unfold sck gsum
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases Nat.eq_zero_or_pos (k - 1 - j) with h | h
  · simp [h]
  · rw [show k - 1 - j = (k - 2 - j) + 1 by omega, pow_succ]
    calc y * (((k - 2 - j + 1 : ℕ) : ℝ≥0∞) * (x ^ j * y ^ (k - 2 - j)))
        = ((k - 2 - j + 1 : ℕ) : ℝ≥0∞) * (x ^ j * (y ^ (k - 2 - j) * y)) := by ring
      _ ≤ ((k - 1 : ℕ) : ℝ≥0∞) * (x ^ j * (y ^ (k - 2 - j) * y)) := by
        gcongr; omega

theorem pow_eq_add_mul_gsum {x y : ℝ≥0∞} (hxy : x ≤ y) (hy : y ≠ ⊤) (k : ℕ) :
    y ^ k = x ^ k + (y - x) * gsum x y k := by
  induction k with
  | zero => simp [gsum]
  | succ k ih =>
    calc y ^ (k + 1) = y * (x ^ k + (y - x) * gsum x y k) := by rw [pow_succ, ih, mul_comm]
      _ = x ^ k * (x + (y - x)) + (y - x) * (y * gsum x y k) := by
        rw [add_tsub_cancel_of_le hxy]; ring
      _ = x ^ (k + 1) + (y - x) * gsum x y (k + 1) := by rw [gsum_succ']; ring

theorem ofReal_two_pow (n : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ n) = 2 ^ n := by
  rw [ENNReal.ofReal_pow (by norm_num)]; simp

theorem ofReal_sub_le (a b : ℝ) : ENNReal.ofReal a - ENNReal.ofReal b ≤ ENNReal.ofReal (a - b) := by
  rw [tsub_le_iff_right]
  calc ENNReal.ofReal a = ENNReal.ofReal ((a - b) + b) := by ring_nf
    _ ≤ _ := ENNReal.ofReal_add_le

theorem ofReal_ratSum {s : Finset ℕ} {g : ℕ → ℚ} (h : ∀ t ∈ s, 0 ≤ g t) :
    ENNReal.ofReal ((∑ t ∈ s, g t : ℚ) : ℝ) = ∑ t ∈ s, ENNReal.ofReal (g t) := by
  rw [Rat.cast_sum]
  exact ENNReal.ofReal_sum_of_nonneg fun t ht => Rat.cast_nonneg.mpr (h t ht)

theorem ofReal_Lm1 : (2 ^ 19 - 1 : ℝ≥0∞) = ENNReal.ofReal (2 ^ 19 - 1) := by
  rw [ENNReal.ofReal_sub _ zero_le_one, ofReal_two_pow, ENNReal.ofReal_one]

theorem cI_pos : 0 < cI := by norm_num [cI]

theorem cIE_eq : cIE = ENNReal.ofReal (cI : ℝ) := by
  have h : ((cI : ℚ) : ℝ) = 2 ^ 127 / (2 ^ 127 - 2 ^ 19) := by simp [cI]
  rw [h, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_sub _ (by norm_num),
    ofReal_two_pow, ofReal_two_pow, cIE]

namespace Sched

variable (S : Sched)

/-- `ȳ_t` in `ℝ≥0∞`. -/
def yb (t : ℕ) : ℝ≥0∞ := ENNReal.ofReal (S.ybar t)

/-- `p_t` in `ℝ≥0∞`. -/
def pE (t : ℕ) : ℝ≥0∞ := (S.a t : ℝ≥0∞) / 2 ^ S.K

/-- `Σ_{j<L} ȳ_{t+1} ^ j ȳ_t ^ (L - 1 - j)`, so that `(ȳ_t - ȳ_{t+1}) wbar t = Ȳ_t - Ȳ_{t+1}`. -/
def wbar (t : ℕ) : ℝ≥0∞ := gsum (S.yb (t + 1)) (S.yb t) (2 ^ 19)

/-- The second-order sum `sck` at tier `t`. -/
def sckT (t : ℕ) : ℝ≥0∞ := sck (S.yb (t + 1)) (S.yb t) (2 ^ 19)

/-- `f_t = (p_t - 2 ρ_N)⁺` in `ℝ≥0∞`. -/
def fE (t : ℕ) : ℝ≥0∞ := S.pE t - (2 ^ 127 : ℝ≥0∞)⁻¹

/-- `κ₁` in `ℝ≥0∞`. -/
def k1E : ℝ≥0∞ := ENNReal.ofReal S.k1

/-- `H'` in `ℝ≥0∞`. -/
def hpE : ℝ≥0∞ := ENNReal.ofReal S.hp

/-- The budget `K(b) = κ₁ b + H' / (4 I) ((b - b0)⁺) ^ 2`. -/
def Kb (b : ℕ) : ℝ≥0∞ := S.k1E * b + S.hpE / (4 * 2 ^ 127) * ((b - S.b0 : ℕ) : ℝ≥0∞) ^ 2

theorem mass_succ (t : ℕ) : S.mass (t + 1) = S.mass t + (S.N t * S.a t : ℚ) / 2 ^ S.K := by
  simp only [mass, Finset.sum_range_succ, add_div]

theorem mass_mono {s t : ℕ} (h : s ≤ t) : S.mass s ≤ S.mass t := by
  unfold mass
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun _ _ _ => by positivity)
    (by positivity)

theorem mass_nonneg (t : ℕ) : 0 ≤ S.mass t := by unfold mass; positivity

theorem mass_lt_one (hS : S.Valid) {t : ℕ} (ht : t ≤ S.T) : S.mass t < 1 := by
  refine (S.mass_mono ht).trans_lt ?_
  unfold mass
  rw [div_lt_one (by positivity)]
  exact_mod_cast hS.mass_lt

theorem ybar_pos (hS : S.Valid) {t : ℕ} (ht : t ≤ S.T) : 0 < S.ybar t := by
  have := S.mass_lt_one hS ht
  have : (0 : ℚ) < eta0 := by norm_num [eta0]
  unfold ybar; linarith

theorem ybar_anti {s t : ℕ} (h : s ≤ t) : S.ybar t ≤ S.ybar s := by
  unfold ybar; linarith [S.mass_mono h]

theorem ybar_succ (t : ℕ) : S.ybar t = S.ybar (t + 1) + S.N t * S.p t := by
  simp only [ybar, mass_succ, p]; ring

theorem p_nonneg (t : ℕ) : 0 ≤ S.p t := by unfold p; positivity

theorem pE_eq (t : ℕ) : S.pE t = ENNReal.ofReal (S.p t) := by
  rw [pE, p, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ofReal_two_pow]

theorem yb_ne_top (t : ℕ) : S.yb t ≠ ⊤ := ENNReal.ofReal_ne_top

theorem yb_eq (hS : S.Valid) {t : ℕ} (ht : t < S.T) :
    S.yb t = S.yb (t + 1) + (S.N t : ℝ≥0∞) * S.pE t := by
  rw [yb, yb, S.ybar_succ t, Rat.cast_add,
    ENNReal.ofReal_add (Rat.cast_nonneg.mpr (S.ybar_pos hS (Nat.succ_le_of_lt ht)).le)
      (Rat.cast_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (S.p_nonneg t))),
    pE_eq, Rat.cast_mul, Rat.cast_natCast, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

theorem yb_succ_le (hS : S.Valid) {t : ℕ} (ht : t < S.T) : S.yb (t + 1) ≤ S.yb t := by
  rw [S.yb_eq hS ht]; exact le_self_add

theorem Hterm_nonneg (hS : S.Valid) {t : ℕ} (ht : t < S.T) : 0 ≤ S.Yu t - S.Yl (t + 1) := by
  have h1 := hS.Yu_ge t ht.le
  have h2 := hS.Yl_le (t + 1) ht
  have h3 : S.ybar (t + 1) ^ 2 ^ 19 ≤ S.ybar t ^ 2 ^ 19 :=
    pow_le_pow_left₀ (S.ybar_pos hS ht).le (S.ybar_anti (Nat.le_succ t)) _
  linarith

/-- `N_t p_t wbar_t = Ȳ_t - Ȳ_{t+1}` for the exact powers. -/
theorem Np_mul_wbar (hS : S.Valid) {t : ℕ} (ht : t < S.T) :
    (S.N t : ℝ≥0∞) * S.pE t * S.wbar t = S.yb t ^ 2 ^ 19 - S.yb (t + 1) ^ 2 ^ 19 := by
  have h := pow_eq_add_mul_gsum (S.yb_succ_le hS ht) (S.yb_ne_top t) (2 ^ 19)
  have hd : S.yb t - S.yb (t + 1) = (S.N t : ℝ≥0∞) * S.pE t := by
    rw [S.yb_eq hS ht, ENNReal.add_sub_cancel_left (S.yb_ne_top _)]
  rw [hd] at h
  exact ENNReal.eq_sub_of_add_eq (ENNReal.pow_ne_top (S.yb_ne_top _))
    (by rw [add_comm]; exact h.symm)

theorem yb_pow_le_Yu (hS : S.Valid) {t : ℕ} (ht : t ≤ S.T) :
    S.yb t ^ 2 ^ 19 ≤ ENNReal.ofReal (S.Yu t) := by
  rw [yb, ← ENNReal.ofReal_pow (Rat.cast_nonneg.mpr (S.ybar_pos hS ht).le)]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hS.Yu_ge t ht)

theorem Yl_le_yb_pow (hS : S.Valid) {t : ℕ} (ht : t ≤ S.T) :
    ENNReal.ofReal (S.Yl t) ≤ S.yb t ^ 2 ^ 19 := by
  rw [yb, ← ENNReal.ofReal_pow (Rat.cast_nonneg.mpr (S.ybar_pos hS ht).le)]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hS.Yl_le t ht)

theorem yb_pow_sub_le (hS : S.Valid) {t : ℕ} (ht : t < S.T) :
    S.yb t ^ 2 ^ 19 - S.yb (t + 1) ^ 2 ^ 19 ≤ ENNReal.ofReal ((S.Yu t - S.Yl (t + 1) : ℚ) : ℝ) :=
  (tsub_le_tsub (S.yb_pow_le_Yu hS ht.le) (S.Yl_le_yb_pow hS ht)).trans
    (by rw [Rat.cast_sub]; exact ofReal_sub_le _ _)

theorem sum_wbar_le (hS : S.Valid) :
    ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.wbar t ≤ ENNReal.ofReal S.Hsum := by
  rw [Hsum, ofReal_ratSum fun t ht =>
    mul_nonneg (S.p_nonneg t) (S.Hterm_nonneg hS (Finset.mem_range.mp ht))]
  refine Finset.sum_le_sum fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  rw [Rat.cast_mul, ENNReal.ofReal_mul (Rat.cast_nonneg.mpr (S.p_nonneg t)), ← pE_eq]
  calc (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.wbar t
      = S.pE t * ((S.N t : ℝ≥0∞) * S.pE t * S.wbar t) := by ring
    _ ≤ _ := by rw [S.Np_mul_wbar hS ht]; gcongr; exact S.yb_pow_sub_le hS ht

theorem sum_sck_le (hS : S.Valid) :
    ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.sckT t ≤
      (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum := by
  rw [SCsum, ofReal_ratSum fun t ht =>
    div_nonneg (mul_nonneg (S.p_nonneg t) (S.Hterm_nonneg hS (Finset.mem_range.mp ht)))
      (hS.yl_pos t (Finset.mem_range.mp ht)).le, Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  have hyl : (0 : ℝ) < S.yl t := Rat.cast_pos.mpr (hS.yl_pos t ht)
  rw [Rat.cast_div, ENNReal.ofReal_div_of_pos hyl, Rat.cast_mul,
    ENNReal.ofReal_mul (Rat.cast_nonneg.mpr (S.p_nonneg t)), ← pE_eq]
  have hL : ((2 ^ 19 - 1 : ℕ) : ℝ≥0∞) = 2 ^ 19 - 1 := by
    rw [ENNReal.natCast_sub]; norm_num
  have hy : ENNReal.ofReal (S.yl t) ≤ S.yb t :=
    ENNReal.ofReal_le_ofReal (by exact_mod_cast hS.yl_le t ht)
  have hsck : S.sckT t * ENNReal.ofReal (S.yl t) ≤ (2 ^ 19 - 1) * S.wbar t := by
    calc S.sckT t * ENNReal.ofReal (S.yl t) ≤ S.yb t * S.sckT t := by rw [mul_comm]; gcongr
      _ ≤ _ := by rw [← hL]; exact y_mul_sck_le _ _ _
  have hne : ENNReal.ofReal (S.yl t) ≠ 0 := by simpa using hyl
  have hsck' : S.sckT t ≤ (2 ^ 19 - 1) * S.wbar t / ENNReal.ofReal (S.yl t) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)]; exact hsck
  calc (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.sckT t
      ≤ (S.N t : ℝ≥0∞) * S.pE t ^ 2 * ((2 ^ 19 - 1) * S.wbar t / ENNReal.ofReal (S.yl t)) := by
        gcongr
    _ = (2 ^ 19 - 1) *
        (S.pE t * ((S.N t : ℝ≥0∞) * S.pE t * S.wbar t) / ENNReal.ofReal (S.yl t)) := by
        simp only [div_eq_mul_inv]; ring
    _ ≤ _ := by rw [S.Np_mul_wbar hS ht]; gcongr; exact S.yb_pow_sub_le hS ht

theorem f_nonneg (t : ℕ) : 0 ≤ S.f t := le_max_left _ _

theorem f_pred_le (hS : S.Valid) {t : ℕ} (ht : t < S.T) (h0 : t ≠ 0) : S.f (t - 1) ≤ S.f t := by
  unfold f p
  gcongr
  exact_mod_cast (hS.a_lt (t - 1) t (by omega) ht).le

theorem fE_eq (t : ℕ) : S.fE t = ENNReal.ofReal (S.f t) := by
  have h : ENNReal.ofReal ((S.f t : ℚ) : ℝ) = ENNReal.ofReal ((S.p t - 1 / 2 ^ 127 : ℚ) : ℝ) := by
    rw [f]
    rcases le_total 0 (S.p t - 1 / 2 ^ 127) with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, Rat.cast_zero, ENNReal.ofReal_zero, eq_comm, ENNReal.ofReal_eq_zero]
      exact_mod_cast h
  have hc : ENNReal.ofReal (((1 : ℚ) / 2 ^ 127 : ℚ) : ℝ) = (2 ^ 127 : ℝ≥0∞)⁻¹ := by
    rw [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat, one_div,
      ENNReal.ofReal_inv_of_pos (by positivity), ofReal_two_pow]
  rw [h, fE, pE_eq, Rat.cast_sub, ENNReal.ofReal_sub _ (by positivity), ← hc]

theorem Pos_term_nonneg (hS : S.Valid) {t : ℕ} (ht : t < S.T) :
    0 ≤ (S.f t - if t = 0 then 0 else S.f (t - 1)) * min 1 (S.Yu t) := by
  apply mul_nonneg
  · split_ifs with h
    · simpa using S.f_nonneg t
    · linarith [S.f_pred_le hS ht h]
  · have := hS.Yu_ge t ht.le
    have := pow_nonneg (S.ybar_pos hS ht.le).le (2 ^ 19)
    exact le_min zero_le_one (by linarith)

theorem sum_pos_le (hS : S.Valid) :
    ∑ t ∈ Finset.range S.T, (S.fE t - (if t = 0 then 0 else S.fE (t - 1))) *
      min 1 (S.yb t ^ 2 ^ 19) ≤ ENNReal.ofReal S.Pos := by
  rw [Pos, ofReal_ratSum fun t ht => S.Pos_term_nonneg hS (Finset.mem_range.mp ht)]
  refine Finset.sum_le_sum fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  have hd : 0 ≤ S.f t - if t = 0 then 0 else S.f (t - 1) := by
    split_ifs with h
    · simpa using S.f_nonneg t
    · linarith [S.f_pred_le hS ht h]
  rw [Rat.cast_mul, ENNReal.ofReal_mul (Rat.cast_nonneg.mpr hd)]
  refine mul_le_mul' ?_ ?_
  · split_ifs with h
    · simp [fE_eq]
    · rw [fE_eq, fE_eq, Rat.cast_sub]; exact ofReal_sub_le _ _
  · rcases le_total 1 (S.Yu t) with h | h
    · rw [min_eq_left h, Rat.cast_one, ENNReal.ofReal_one]; exact min_le_left _ _
    · rw [min_eq_right h]; exact (min_le_right _ _).trans (S.yb_pow_le_Yu hS ht.le)

theorem fE_mono (hS : S.Valid) {t : ℕ} (ht : t + 1 < S.T) : S.fE t ≤ S.fE (t + 1) := by
  unfold fE pE
  gcongr
  exact_mod_cast (hS.a_lt t (t + 1) (by omega) ht).le

theorem fE_telescope (hS : S.Valid) {τ : ℕ} (hτ : τ < S.T) :
    S.fE τ = ∑ t ∈ Finset.range (τ + 1), (S.fE t - if t = 0 then 0 else S.fE (t - 1)) := by
  induction τ with
  | zero => simp
  | succ τ ih =>
    rw [Finset.sum_range_succ, ← ih (by omega), if_neg (by omega), Nat.add_sub_cancel,
      add_tsub_cancel_of_le (S.fE_mono hS hτ)]

theorem Hsum_nonneg (hS : S.Valid) : 0 ≤ S.Hsum :=
  Finset.sum_nonneg fun t ht =>
    mul_nonneg (S.p_nonneg t) (S.Hterm_nonneg hS (Finset.mem_range.mp ht))

theorem SCsum_nonneg (hS : S.Valid) : 0 ≤ S.SCsum :=
  Finset.sum_nonneg fun t ht =>
    div_nonneg (mul_nonneg (S.p_nonneg t) (S.Hterm_nonneg hS (Finset.mem_range.mp ht)))
      (hS.yl_pos t (Finset.mem_range.mp ht)).le

theorem Pos_nonneg (hS : S.Valid) : 0 ≤ S.Pos :=
  Finset.sum_nonneg fun _ ht => S.Pos_term_nonneg hS (Finset.mem_range.mp ht)

theorem hp_nonneg (hS : S.Valid) : 0 ≤ S.hp := by
  refine le_trans ?_ hS.hp_ge
  have := S.Hsum_nonneg hS
  have := S.SCsum_nonneg hS
  have := cI_pos
  unfold Hprime Hbar SCf
  positivity

theorem k1_nonneg (hS : S.Valid) : 0 ≤ S.k1 := by
  refine le_trans ?_ hS.k1_post
  have := S.Pos_nonneg hS
  unfold kpost
  positivity

/-- `c^2 (L - 1) SCsum` in `ℝ≥0∞`. -/
theorem ofReal_SCf :
    ENNReal.ofReal ((cI : ℝ) ^ 2 * (2 ^ 19 - 1) * S.SCsum) =
      cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum := by
  have hc : (0 : ℝ) ≤ cI := Rat.cast_nonneg.mpr cI_pos.le
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hc, cIE_eq, ofReal_Lm1]

theorem Hprime_le (hS : S.Valid) :
    cIE * ENNReal.ofReal S.Hsum + cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum / 2 ^ 127 ≤
      S.hpE := by
  have hc : (0 : ℝ) ≤ cI := Rat.cast_nonneg.mpr cI_pos.le
  have hH : (0 : ℝ) ≤ S.Hsum := Rat.cast_nonneg.mpr (S.Hsum_nonneg hS)
  have hSC : (0 : ℝ) ≤ S.SCsum := Rat.cast_nonneg.mpr (S.SCsum_nonneg hS)
  rw [← S.ofReal_SCf, ← ofReal_two_pow, ← ENNReal.ofReal_div_of_pos (by positivity), cIE_eq,
    ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (by positivity) (by positivity), hpE]
  apply ENNReal.ofReal_le_ofReal
  have := hS.hp_ge
  unfold Hprime Hbar SCf at this
  exact_mod_cast this

theorem SCf_le (hS : S.Valid) :
    cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum ≤ 2 * 2 ^ 19 * S.k1E := by
  rw [← S.ofReal_SCf, k1E, ← ofReal_two_pow, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h := (Rat.cast_le (K := ℝ)).mpr hS.k1_sc
  unfold SCf at h
  push_cast at h
  linarith

theorem kpost_le (hS : S.Valid) : (2 ^ 128 : ℝ≥0∞)⁻¹ + ENNReal.ofReal S.Pos / 2 ≤ S.k1E := by
  have hP : (0 : ℝ) ≤ S.Pos := Rat.cast_nonneg.mpr (S.Pos_nonneg hS)
  rw [← ofReal_two_pow, ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_div_of_pos (by norm_num), ← ENNReal.ofReal_add (by positivity)
      (by positivity), k1E]
  apply ENNReal.ofReal_le_ofReal
  have h := (Rat.cast_le (K := ℝ)).mpr hS.k1_post
  unfold kpost at h
  push_cast at h
  rw [← one_div]
  linarith

theorem rate_le_k1 (hS : S.Valid) : (2 ^ 128 : ℝ≥0∞)⁻¹ ≤ S.k1E :=
  le_self_add.trans (S.kpost_le hS)

theorem k1E_ne_top : S.k1E ≠ ⊤ := ENNReal.ofReal_ne_top

theorem hpE_ne_top : S.hpE ≠ ⊤ := ENNReal.ofReal_ne_top

theorem Kb_mono {b b' : ℕ} (h : b ≤ b') : S.Kb b ≤ S.Kb b' := by
  unfold Kb
  gcongr

theorem Kb_step {n b : ℕ} (h : n ≤ b) : S.Kb (b - n) + S.k1E * n ≤ S.Kb b := by
  unfold Kb
  have hb : ((b - n : ℕ) : ℝ≥0∞) + n = b := by rw [← Nat.cast_add, Nat.sub_add_cancel h]
  calc S.k1E * ((b - n : ℕ) : ℝ≥0∞) + S.hpE / (4 * 2 ^ 127) * ((b - n - S.b0 : ℕ) : ℝ≥0∞) ^ 2 +
        S.k1E * n
      = S.k1E * b + S.hpE / (4 * 2 ^ 127) * ((b - n - S.b0 : ℕ) : ℝ≥0∞) ^ 2 := by
        rw [← hb]; ring
    _ ≤ _ := by gcongr; omega

theorem Kb_eq (hS : S.Valid) (b : ℕ) :
    S.Kb b = ENNReal.ofReal ((S.k1 : ℝ) * b + (S.hp : ℝ) / (4 * 2 ^ 127) *
      ((b - S.b0 : ℕ) : ℝ) ^ 2) := by
  have hk : (0 : ℝ) ≤ S.k1 := Rat.cast_nonneg.mpr (S.k1_nonneg hS)
  have hh : (0 : ℝ) ≤ S.hp := Rat.cast_nonneg.mpr (S.hp_nonneg hS)
  rw [ENNReal.ofReal_add (mul_nonneg hk (Nat.cast_nonneg _))
      (mul_nonneg (div_nonneg hh (by norm_num)) (sq_nonneg _)),
    ENNReal.ofReal_mul hk, ENNReal.ofReal_mul (div_nonneg hh (by norm_num)),
    ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat, ofReal_two_pow, Kb, k1E, hpE]

theorem Kb_step_enc (hS : S.Valid) {b : ℕ} (hb : 2 ≤ b) :
    S.Kb (b - 2) + (1 + ((b - 2 : ℕ) : ℝ≥0∞) / 2 ^ 127) * S.hpE ≤ S.Kb b := by
  have hk : (0 : ℝ) ≤ S.k1 := Rat.cast_nonneg.mpr (S.k1_nonneg hS)
  have hh : (0 : ℝ) ≤ S.hp := Rat.cast_nonneg.mpr (S.hp_nonneg hS)
  have hE : (1 + ((b - 2 : ℕ) : ℝ≥0∞) / 2 ^ 127) =
      ENNReal.ofReal (1 + ((b - 2 : ℕ) : ℝ) / 2 ^ 127) := by
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ofReal_two_pow]
  rw [S.Kb_eq hS, S.Kb_eq hS, hpE, hE, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hk (Nat.cast_nonneg _))
      (mul_nonneg (div_nonneg hh (by norm_num)) (sq_nonneg _))) (mul_nonneg (by positivity) hh)]
  apply ENNReal.ofReal_le_ofReal
  have hb0 : (S.hp : ℝ) * ((S.b0 : ℝ) - 1) ≤ 2 ^ 127 * (2 * S.k1 - S.hp) := by
    exact_mod_cast hS.b0_le
  have hb2 : ((b - 2 : ℕ) : ℝ) = b - 2 := by rw [Nat.cast_sub hb]; norm_num
  rcases le_or_gt b (S.b0 + 1) with h | h
  · rw [show b - 2 - S.b0 = 0 by omega, hb2]
    have hB : (b : ℝ) - 2 ≤ S.b0 - 1 := by
      have : (b : ℝ) ≤ S.b0 + 1 := by exact_mod_cast h
      linarith
    have : ((b : ℝ) - 2) * S.hp / 2 ^ 127 ≤ 2 * S.k1 - S.hp := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hQ := mul_nonneg (div_nonneg hh (by norm_num : (0 : ℝ) ≤ 4 * 2 ^ 127))
      (sq_nonneg ((b - S.b0 : ℕ) : ℝ))
    push_cast
    have : (1 + ((b : ℝ) - 2) / 2 ^ 127) * S.hp = S.hp + ((b : ℝ) - 2) * S.hp / 2 ^ 127 := by
      ring
    linarith
  · rw [Nat.cast_sub (by omega : S.b0 ≤ b - 2), Nat.cast_sub (by omega : S.b0 ≤ b), hb2]
    have : ((S.b0 : ℝ) - 1) * S.hp / 2 ^ 127 ≤ 2 * S.k1 - S.hp := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hsq : (S.hp : ℝ) / (4 * 2 ^ 127) * ((b : ℝ) - S.b0) ^ 2 -
        S.hp / (4 * 2 ^ 127) * ((b : ℝ) - 2 - S.b0) ^ 2 =
        ((b : ℝ) - 2) * S.hp / 2 ^ 127 - ((S.b0 : ℝ) - 1) * S.hp / 2 ^ 127 := by
      field_simp; ring
    have : (1 + ((b : ℝ) - 2) / 2 ^ 127) * S.hp = S.hp + ((b : ℝ) - 2) * S.hp / 2 ^ 127 := by
      ring
    linarith

theorem Kb_le (hS : S.Valid) {b : ℕ} (hb : b ≤ 2 ^ 127) :
    S.Kb b ≤ (2 ^ 127 : ℝ≥0∞)⁻¹ * b := by
  have hh : (0 : ℝ) ≤ S.hp := Rat.cast_nonneg.mpr (S.hp_nonneg hS)
  have hR : (2 ^ 127 : ℝ≥0∞)⁻¹ * b = ENNReal.ofReal ((b : ℝ) / 2 ^ 127) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ofReal_two_pow,
      div_eq_mul_inv, mul_comm]
  rw [S.Kb_eq hS, hR]
  apply ENNReal.ofReal_le_ofReal
  have hk : (S.k1 : ℝ) + S.hp / (4 * 2 ^ 127) * ((2 ^ 127 - S.b0 : ℕ) : ℝ) ^ 2 / 2 ^ 127 ≤
      1 / 2 ^ 127 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hS.kmax_le
    push_cast at h
    linarith
  have hsq : ((b - S.b0 : ℕ) : ℝ) ^ 2 ≤ ((2 ^ 127 - S.b0 : ℕ) : ℝ) ^ 2 / 2 ^ 127 * b := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rcases le_or_gt b S.b0 with h | h
    · rw [Nat.sub_eq_zero_of_le h]; norm_num; positivity
    · have hB : S.b0 ≤ 2 ^ 127 := by omega
      have hbI : (b : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hb
      have hbB : (S.b0 : ℝ) < b := by exact_mod_cast h
      rw [Nat.cast_sub h.le, Nat.cast_sub hB, Nat.cast_pow, Nat.cast_ofNat]
      have hB0 : (0 : ℝ) ≤ S.b0 := Nat.cast_nonneg _
      generalize (2 : ℝ) ^ 127 = I at hbI ⊢
      have hu : 0 < (b : ℝ) - S.b0 := by linarith
      have huv : (b : ℝ) - S.b0 ≤ I - S.b0 := by linarith
      nlinarith [mul_nonneg (mul_nonneg hu.le (hu.le.trans huv)) (sub_nonneg.2 huv),
        mul_le_mul_of_nonneg_left (mul_self_le_mul_self hu.le huv) hB0]
  have hA : (0 : ℝ) ≤ S.hp / (4 * 2 ^ 127) := div_nonneg hh (by norm_num)
  have h1 := mul_le_mul_of_nonneg_left hsq hA
  have h2 := mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  have e1 : (S.hp : ℝ) / (4 * 2 ^ 127) * (((2 ^ 127 - S.b0 : ℕ) : ℝ) ^ 2 / 2 ^ 127 * b) =
      S.hp / (4 * 2 ^ 127) * ((2 ^ 127 - S.b0 : ℕ) : ℝ) ^ 2 / 2 ^ 127 * b := by ring
  have e2 : (1 : ℝ) / 2 ^ 127 * b = b / 2 ^ 127 := by ring
  nlinarith

end Sched

end OptimalOTS.LeanIsaBaseline.Layer.Tier
