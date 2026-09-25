import Submissions.UpperLeanIsa.TierRow

/-!
# The RowGood supermartingale

With `λ = 2 ^ -56`, `Psi d` sums over the rows `M` and the tiers `t < T` the moment
`exp (-λ rowN) / psiD t ^ rowU`, where `psiD t = E exp (-λ X)` for `X ~ Bernoulli(P_{≤t})`
(tier-proof.md §8). `PsiE = Psi / exp 1000`.

* `PsiE_enc` (R1): a fresh index answer leaves `PsiE` unchanged on average;
* `PsiE_of_ne`: a non-index answer leaves `PsiE` unchanged;
* `PsiE_noEnc`: without index entries `PsiE ≤ 2 ^ -500`;
* `one_le_PsiE` (R2): a bad row of at most `2 ^ 126` nonces gives `PsiE ≥ 1`.
-/

noncomputable section

open OracleSpec

open scoped Classical ENNReal

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Params

/-- λ = 2^-56 -/
def lam : ℝ := (2 ^ 56 : ℝ)⁻¹

/-- E e^{-λ X} for X ~ Bernoulli(P_{≤t}) -/
def psiD (S : Tier.Sched) (t : ℕ) : ℝ :=
  1 - (S.mass (t + 1) : ℝ) + (S.mass (t + 1) : ℝ) * Real.exp (-lam)

/-- The RowGood threshold. -/
def thetaRG : ℝ := Real.exp 1000

variable (P : Params) (S : Tier.Sched)

/-- The moment of tier `t` of row `M`. -/
def psiRow (d : Cache) (M : EMessage) (t : ℕ) : ℝ :=
  Real.exp (-(lam * P.rowN S d M t)) / psiD S t ^ P.rowU d M

/-- The RowGood potential. -/
def Psi (d : Cache) : ℝ := ∑ M : EMessage, ∑ t ∈ Finset.range S.T, P.psiRow S d M t

/-- The normalized RowGood potential. -/
def PsiE (d : Cache) : ℝ≥0∞ := ENNReal.ofReal (P.Psi S d / thetaRG)

variable {P S}

/-! ## The mass and `psiD` -/

theorem psi_mass_nonneg (t : ℕ) : (0 : ℝ) ≤ S.mass t := by
  unfold Tier.Sched.mass
  push_cast
  positivity

theorem psi_mass_mono {s t : ℕ} (h : s ≤ t) : (S.mass s : ℝ) ≤ S.mass t := by
  unfold Tier.Sched.mass
  push_cast
  gcongr ?_ / _
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun _ _ _ => by positivity)

theorem psi_mass_T_lt_one (hS : S.Valid) : (S.mass S.T : ℝ) < 1 := by
  have h : (∑ t ∈ Finset.range S.T, (S.N t * S.a t : ℝ)) < 2 ^ S.K := by
    exact_mod_cast hS.mass_lt
  unfold Tier.Sched.mass
  push_cast
  rw [div_lt_one (by positivity)]
  exact h

theorem psiD_pos (hS : S.Valid) {t : ℕ} (ht : t < S.T) : 0 < psiD S t := by
  have h1 := psi_mass_mono (S := S) (show t + 1 ≤ S.T by omega)
  have h2 := psi_mass_T_lt_one hS
  have h3 := mul_nonneg (psi_mass_nonneg (S := S) (t + 1)) (Real.exp_pos (-lam)).le
  unfold psiD
  linarith

theorem psiRow_nonneg (hS : S.Valid) (d : Cache) (M : EMessage) {t : ℕ} (ht : t < S.T) :
    0 ≤ P.psiRow S d M t := by
  have := psiD_pos hS ht
  unfold psiRow
  positivity

theorem Psi_nonneg (hS : S.Valid) (d : Cache) : 0 ≤ P.Psi S d :=
  Finset.sum_nonneg fun M _ => Finset.sum_nonneg fun _ ht =>
    psiRow_nonneg hS d M (Finset.mem_range.1 ht)

/-! ## A fresh index answer -/

section Fresh

variable {c : Cache} {M₀ : EMessage} {η₀ : Nonce}

theorem psi_card_filter_insert {p p' : Nonce → Prop} [DecidablePred p] [DecidablePred p']
    (b : Prop) [Decidable b] (h0 : ¬ p η₀) (h : ∀ η, p' η ↔ (η = η₀ ∧ b) ∨ p η) :
    (Finset.univ.filter p').card = (Finset.univ.filter p).card + if b then 1 else 0 := by
  by_cases hb : b
  · rw [if_pos hb, ← Finset.card_insert_of_notMem (s := Finset.univ.filter p) (a := η₀)
      (by simp [h0])]
    exact congrArg Finset.card (Finset.ext fun η => by simp [h, hb])
  · rw [if_neg hb, add_zero]
    exact congrArg Finset.card (Finset.ext fun η => by simp [h, hb])

theorem psi_upd_apply (w : BitVec hashBits) (M : EMessage) (η : Nonce) :
    (c.cacheQuery (P.encQuery (M₀ ++ η₀)) w) (P.encQuery (M ++ η)) =
      if M = M₀ ∧ η = η₀ then some w else c (P.encQuery (M ++ η)) := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact QueryCache.cacheQuery_self _ _ _
  · exact QueryCache.cacheQuery_of_ne _ _ fun he => h (append_pair_inj (P.encQuery_inj he))

variable (hq : c (P.encQuery (M₀ ++ η₀)) = none)
include hq

theorem rowU_upd (w : BitVec hashBits) (M : EMessage) :
    P.rowU (c.cacheQuery (P.encQuery (M₀ ++ η₀)) w) M =
      P.rowU c M + if M = M₀ then 1 else 0 := by
  unfold rowU
  by_cases hM : M = M₀
  · subst hM
    refine psi_card_filter_insert (η₀ := η₀) _ (by simp [hq]) fun η => ?_
    by_cases hη : η = η₀
    · subst hη; simp
    · simp [psi_upd_apply, hη]
  · rw [if_neg hM, add_zero]
    exact congrArg Finset.card (Finset.ext fun η => by simp [psi_upd_apply, hM])

theorem rowN_upd (w : BitVec hashBits) (M : EMessage) (t : ℕ) :
    P.rowN S (c.cacheQuery (P.encQuery (M₀ ++ η₀)) w) M t =
      P.rowN S c M t + if M = M₀ ∧ P.tierW S w ≤ t then 1 else 0 := by
  unfold rowN
  by_cases hM : M = M₀
  · subst hM
    refine psi_card_filter_insert (η₀ := η₀) _ (by simp [hq]) fun η => ?_
    by_cases hη : η = η₀
    · subst hη; simp [hq]
    · simp [psi_upd_apply, hη]
  · rw [if_neg (fun h => hM h.1), add_zero]
    exact congrArg Finset.card (Finset.ext fun η => by simp [psi_upd_apply, hM])

theorem psiRow_upd (hS : S.Valid) (w : BitVec hashBits) (M : EMessage) {t : ℕ} (ht : t < S.T) :
    P.psiRow S (c.cacheQuery (P.encQuery (M₀ ++ η₀)) w) M t =
      P.psiRow S c M t * if M = M₀ then
        (if P.tierW S w ≤ t then Real.exp (-lam) else 1) / psiD S t else 1 := by
  have hD := (psiD_pos hS ht).ne'
  unfold psiRow
  rw [rowU_upd hq, rowN_upd hq]
  by_cases hM : M = M₀
  · simp only [hM, true_and, if_true]
    split_ifs with hw
    · push_cast
      rw [mul_add, neg_add, Real.exp_add, mul_one, pow_succ]
      field_simp
    · simp only [add_zero, pow_succ]
      field_simp
  · rw [if_neg hM, if_neg hM, if_neg (fun h => hM h.1), add_zero, add_zero, mul_one]

end Fresh

theorem psi_sum_tierW (hS : S.Valid) (hT : P.TierHyp S) {t : ℕ} (ht : t < S.T) :
    ∑ w : BitVec hashBits, (if P.tierW S w ≤ t then Real.exp (-lam) else 1) =
      (Fintype.card (BitVec hashBits) : ℝ) * psiD S t := by
  have hc := card_tierW_lt hS hT (show t + 1 ≤ S.T by omega)
  simp only [Nat.lt_add_one_iff] at hc
  have hn := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun w : BitVec hashBits => P.tierW S w ≤ t)
  have hcard : (Fintype.card (BitVec hashBits) : ℝ) = 2 ^ 256 := by
    rw [Fintype.card_bitVec]; norm_num [hashBits]
  rw [Finset.card_univ] at hn
  have hn' : ((Finset.univ.filter fun w : BitVec hashBits => P.tierW S w ≤ t).card : ℝ) +
      (Finset.univ.filter fun w : BitVec hashBits => ¬ P.tierW S w ≤ t).card = 2 ^ 256 := by
    rw [← hcard]; exact_mod_cast hn
  have hc' : ((Finset.univ.filter fun w : BitVec hashBits => P.tierW S w ≤ t).card : ℝ) =
      (∑ s ∈ Finset.range (t + 1), (S.N s * S.a s : ℝ)) * 2 ^ 129 := by
    exact_mod_cast hc
  have hm : (S.mass (t + 1) : ℝ) =
      (∑ s ∈ Finset.range (t + 1), (S.N s * S.a s : ℝ)) / 2 ^ 127 := by
    unfold Tier.Sched.mass
    rw [hT.K_eq]
    push_cast
    rfl
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one,
    hcard]
  unfold psiD
  rw [hm, show ((Finset.univ.filter fun w : BitVec hashBits => ¬ P.tierW S w ≤ t).card : ℝ) =
    2 ^ 256 - (Finset.univ.filter fun w : BitVec hashBits => P.tierW S w ≤ t).card by
      linarith, hc']
  ring

theorem psi_sum_psiRow (hS : S.Valid) (hT : P.TierHyp S) {c : Cache} {M₀ : EMessage}
    {η₀ : Nonce} (hq : c (P.encQuery (M₀ ++ η₀)) = none) (M : EMessage) {t : ℕ}
    (ht : t < S.T) :
    ∑ w : BitVec hashBits, P.psiRow S (c.cacheQuery (P.encQuery (M₀ ++ η₀)) w) M t =
      (Fintype.card (BitVec hashBits) : ℝ) * P.psiRow S c M t := by
  have hD := (psiD_pos hS ht).ne'
  simp_rw [psiRow_upd hq hS _ M ht]
  by_cases hM : M = M₀
  · simp only [hM, if_true]
    rw [← Finset.mul_sum, ← Finset.sum_div, psi_sum_tierW hS hT ht]
    field_simp
  · simp [hM, mul_comm]

theorem psi_sum_Psi (hS : S.Valid) (hT : P.TierHyp S) {c : Cache} {M₀ : EMessage}
    {η₀ : Nonce} (hq : c (P.encQuery (M₀ ++ η₀)) = none) :
    ∑ w : BitVec hashBits, P.Psi S (c.cacheQuery (P.encQuery (M₀ ++ η₀)) w) =
      (Fintype.card (BitVec hashBits) : ℝ) * P.Psi S c := by
  unfold Psi
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t ht => psi_sum_psiRow hS hT hq M (Finset.mem_range.1 ht)

theorem PsiE_enc (hS : S.Valid) (hT : P.TierHyp S) {c : Cache} {u₀ : EncInput}
    (hq : c (P.encQuery u₀) = none) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      P.PsiE S (c.cacheQuery (P.encQuery u₀) w) = P.PsiE S c := by
  obtain ⟨M₀, η₀, rfl⟩ := exists_append u₀
  have hK : (0 : ℝ) < Fintype.card (BitVec hashBits) := by exact_mod_cast Fintype.card_pos
  have hθ : 0 < thetaRG := Real.exp_pos _
  have hcard : (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal (Fintype.card (BitVec hashBits) : ℝ)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hK, ENNReal.ofReal_natCast]
  unfold PsiE
  rw [hcard]
  simp_rw [← ENNReal.ofReal_mul (inv_nonneg.2 hK.le)]
  rw [← ENNReal.ofReal_sum_of_nonneg fun w _ =>
    mul_nonneg (inv_nonneg.2 hK.le) (div_nonneg (Psi_nonneg hS _) hθ.le)]
  refine congrArg ENNReal.ofReal ?_
  rw [← Finset.mul_sum, ← Finset.sum_div, psi_sum_Psi hS hT hq]
  field_simp

/-! ## Non-index answers and caches without index entries -/

theorem PsiE_of_ne {c : Cache} {q : Query} (hq : ∀ u, q ≠ P.encQuery u) (w : BitVec hashBits) :
    P.PsiE S (c.cacheQuery q w) = P.PsiE S c := by
  have h : ∀ u, (c.cacheQuery q w) (P.encQuery u) = c (P.encQuery u) :=
    fun u => QueryCache.cacheQuery_of_ne _ _ (hq u).symm
  simp only [PsiE, Psi, psiRow, rowU, rowN, h]

theorem PsiE_noEnc (hS : S.Valid) {c : Cache} (hc : ∀ u, c (P.encQuery u) = none) :
    P.PsiE S c ≤ (2 ^ 500 : ℝ≥0∞)⁻¹ := by
  have hU : ∀ M, P.rowU c M = 0 := fun M => by
    unfold rowU
    simp [hc]
  have hN : ∀ M t, P.rowN S c M t = 0 := fun M t => by
    unfold rowN
    simp [hc]
  have hPsi : P.Psi S c = 2 ^ 384 * S.T := by
    simp only [Psi, psiRow, hU, hN, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, pow_zero,
      div_one, Finset.sum_const, Finset.card_range, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Fintype.card_bitVec, show emsgBits = 384 from rfl, Nat.cast_pow, Nat.cast_ofNat]
  have hT : (S.T : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hS.T_le
  have hθ : (2 : ℝ) ^ 1000 ≤ thetaRG := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) ^ 1000 ≤ Real.exp 1 ^ 1000 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = thetaRG := by rw [thetaRG, ← Real.exp_nat_mul]; norm_num
  have hle : P.Psi S c / thetaRG ≤ (2 ^ 500 : ℝ)⁻¹ := by
    calc P.Psi S c / thetaRG ≤ 2 ^ 448 / 2 ^ 1000 := by
          rw [hPsi]
          gcongr
          calc (2 : ℝ) ^ 384 * S.T ≤ 2 ^ 384 * 2 ^ 64 := by gcongr
            _ = 2 ^ 448 := by rw [← pow_add]
      _ ≤ (2 ^ 500 : ℝ)⁻¹ := by
          rw [div_le_iff₀ (by positivity), show (2 : ℝ) ^ 1000 = 2 ^ 500 * 2 ^ 500 by
            rw [← pow_add], ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
          exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  unfold PsiE
  calc ENNReal.ofReal (P.Psi S c / thetaRG) ≤ ENNReal.ofReal (2 ^ 500 : ℝ)⁻¹ :=
        ENNReal.ofReal_le_ofReal hle
    _ = (2 ^ 500 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat]

/-! ## A bad row -/

theorem thetaRG_le_psiRow (hS : S.Valid) {c : Cache} {M : EMessage} {t : ℕ} (ht : t < S.T)
    (hu : P.rowU c M ≤ 2 ^ 126)
    (hbad : (P.rowN S c M t : ℝ) + 2 ^ 66 < (P.rowU c M : ℝ) * (S.mass (t + 1) : ℝ)) :
    thetaRG ≤ P.psiRow S c M t := by
  set n : ℝ := (P.rowN S c M t : ℝ)
  set u : ℝ := (P.rowU c M : ℝ) with hu_def
  set m : ℝ := (S.mass (t + 1) : ℝ)
  set e : ℝ := Real.exp (-lam)
  have hlam : lam = 1 / 2 ^ 56 := by rw [lam, one_div]
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hm0 : 0 ≤ m := psi_mass_nonneg (t + 1)
  have hacc : ((S.mass S.T : ℚ) : ℝ) ≤ ((1 / 2 ^ 10 : ℚ) : ℝ) := Rat.cast_le.2 hS.acc_le
  have hm1 : m ≤ 1 / 2 ^ 10 := (psi_mass_mono (show t + 1 ≤ S.T by omega)).trans
    (by simpa using hacc)
  have hu0 : 0 ≤ u := Nat.cast_nonneg _
  have hu1 : u ≤ 2 ^ 126 := by rw [hu_def]; exact_mod_cast hu
  have he : e ≤ 1 - lam + lam ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := -lam)
      (by rw [abs_neg, abs_of_nonneg hlam0, hlam]; norm_num)
    have h' := (abs_le.1 h).2
    rw [neg_sq] at h'
    linarith
  have hum0 : 0 ≤ u * m := mul_nonneg hu0 hm0
  have hum : u * m ≤ 2 ^ 126 * (1 / 2 ^ 10) := mul_le_mul hu1 hm1 hm0 (by norm_num)
  have hz : u * m * (lam - lam ^ 2) ≤ u * m * (1 - e) :=
    mul_le_mul_of_nonneg_left (by linarith) hum0
  have hn : lam * n ≤ lam * (u * m - 2 ^ 66) := mul_le_mul_of_nonneg_left (by linarith) hlam0
  have hl2 : u * m * lam ^ 2 ≤ 2 ^ 126 * (1 / 2 ^ 10) * lam ^ 2 :=
    mul_le_mul_of_nonneg_right hum (sq_nonneg _)
  have hc1 : lam * 2 ^ 66 = 1024 := by rw [hlam]; norm_num
  have hc2 : 2 ^ 126 * (1 / 2 ^ 10) * lam ^ 2 = (16 : ℝ) := by rw [hlam]; norm_num
  have hD : psiD S t = 1 - m * (1 - e) := by unfold psiD; ring
  have hDpos := psiD_pos hS ht
  have hDle : psiD S t ≤ Real.exp (-(m * (1 - e))) := by
    rw [hD]; linarith [Real.add_one_le_exp (-(m * (1 - e)))]
  unfold thetaRG psiRow
  calc Real.exp 1000 ≤ Real.exp (-(lam * n) - P.rowU c M * (-(m * (1 - e)))) := by
        apply Real.exp_le_exp.2
        linarith
    _ = Real.exp (-(lam * n)) / Real.exp (-(m * (1 - e))) ^ P.rowU c M := by
        rw [Real.exp_sub, Real.exp_nat_mul]
    _ ≤ Real.exp (-(lam * n)) / psiD S t ^ P.rowU c M :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos hDpos _)
          (pow_le_pow_left₀ hDpos.le hDle _)

-- `hT` is part of the fixed interface.
set_option linter.unusedVariables false in
theorem one_le_PsiE (hS : S.Valid) (hT : P.TierHyp S) {c : Cache} {M : EMessage}
    (hu : P.rowU c M ≤ 2 ^ 126) (h : ¬ P.RowGood S c M) : 1 ≤ P.PsiE S c := by
  unfold RowGood at h
  simp only [not_forall, not_le, exists_prop] at h
  obtain ⟨t, ht, hbad⟩ := h
  have hrow := thetaRG_le_psiRow hS ht hu hbad
  have hsum : P.psiRow S c M t ≤ P.Psi S c :=
    calc P.psiRow S c M t ≤ ∑ t' ∈ Finset.range S.T, P.psiRow S c M t' :=
          Finset.single_le_sum (f := fun t' => P.psiRow S c M t')
            (fun t' ht' => psiRow_nonneg hS c M (Finset.mem_range.1 ht'))
            (Finset.mem_range.2 ht)
      _ ≤ P.Psi S c :=
          Finset.single_le_sum (f := fun M' => ∑ t' ∈ Finset.range S.T, P.psiRow S c M' t')
            (fun M' _ => Finset.sum_nonneg fun t' ht' =>
              psiRow_nonneg hS c M' (Finset.mem_range.1 ht'))
            (Finset.mem_univ M)
  unfold PsiE
  rw [ENNReal.one_le_ofReal, one_le_div (show 0 < thetaRG from Real.exp_pos _)]
  exact hrow.trans hsum

end Params

end OptimalOTS.LeanIsaBaseline.Layer
