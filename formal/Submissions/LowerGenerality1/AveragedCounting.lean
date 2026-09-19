import Submissions.LowerGenerality1.AveragedSearch
import Submissions.LowerGenerality1.AveragedSigning
import Submissions.LowerGenerality1.Patterns

/-! Cauchy--Schwarz averages over every nonempty reconstruction-pattern class. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 4096

namespace OptimalOTS.AveragedCounting

open OptimalOTS.Dag


attribute [local irreducible] Nat.choose

theorem sum_fiber_hitRate_ge {ι α : Type*} [Fintype ι] [DecidableEq α]
    (f : ι → α) :
    (Fintype.card ι : ℝ) ^ 2 /
        (64 * (Finset.univ.image f).card + Fintype.card ι) ≤
      ∑ i, ((Finset.univ.filter fun j => f j = f i).card : ℝ) /
        (64 + (Finset.univ.filter fun j => f j = f i).card) := by
  classical
  let U := Finset.univ.image f
  let k := fun y => (Finset.univ.filter fun i => f i = y).card
  have hcards : (∑ y ∈ U, (k y : ℝ)) = Fintype.card ι := by
    exact_mod_cast (Finset.card_eq_sum_card_image f Finset.univ).symm
  have he : (∑ i, (k (f i) : ℝ) / (64 + k (f i))) =
      ∑ y ∈ U, (k y : ℝ) ^ 2 / (64 + k y) := by
    have h := Finset.sum_fiberwise_of_maps_to'
      (s := Finset.univ) (t := U) (g := f)
      (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩)
      (fun y => (k y : ℝ) / (64 + k y))
    rw [← h]
    apply Finset.sum_congr rfl
    intro y _
    simp only [Finset.sum_const, nsmul_eq_mul]
    change (k y : ℝ) * ((k y : ℝ) / (64 + k y)) = _
    ring
  change _ ≤ ∑ i, (k (f i) : ℝ) / (64 + k (f i))
  rw [he]
  have h := Finset.sq_sum_div_le_sum_sq_div U (fun y => (k y : ℝ))
    (g := fun y => 64 + (k y : ℝ)) (fun _ _ => by positivity)
  rw [hcards, Finset.sum_add_distrib, hcards] at h
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using h

theorem paper_weighted_rate_ge (S : Scheme)
    (hcount : (Finset.univ.image S.hashPattern).card ≤ Nat.choose 129 42) :
    (1 / 28 : ℝ≥0∞) ≤
      ENNReal.ofReal (FreshSign.rate trials) *
        ∑ i, AveragedSearch.hitRate (S.samePattern i).card := by
  let M : ℝ := 2 ^ 115
  let K : ℝ := Nat.choose 129 42
  have hM : 0 < M := by dsimp [M]; norm_num
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hden : 0 < 64 * K + M :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hK) hM
  have hsum := sum_fiber_hitRate_ge S.hashPattern
  simp only [Fintype.card_fin] at hsum
  change (((2 ^ 115 : ℕ) : ℝ) ^ 2 / (64 * (Finset.univ.image S.hashPattern).card +
    ((2 ^ 115 : ℕ) : ℝ))) ≤ _ at hsum
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hsum
  have hc : ((Finset.univ.image S.hashPattern).card : ℝ) ≤ K := by
    exact Nat.cast_le.mpr hcount
  have hsum' : M ^ 2 / (64 * K + M) ≤
      ∑ i, ((S.samePattern i).card : ℝ) / (64 + (S.samePattern i).card) := by
    apply le_trans _ hsum
    change M ^ 2 / (64 * K + M) ≤
      M ^ 2 / (64 * (Finset.univ.image S.hashPattern).card + M)
    apply div_le_div_of_nonneg_left (sq_nonneg M)
      (add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hM)
    linarith
  have hmul := mul_le_mul AveragedSigning.paper_rate_ge hsum'
    (div_nonneg (sq_nonneg M) hden.le)
    (FreshSign.rate_nonneg (by norm_num [nonceBits, idxBits, numCuts, trials, idxCost, blockCost, signBudget, msgBits, blockBits]) _)
  have hnum : (1 / 28 : ℝ) ≤
      (128 : ℝ) / (129 * 2 ^ 115) * (M ^ 2 / (64 * K + M)) := by
    norm_num [M, K, Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial, Nat.factorial]
  have h := ENNReal.ofReal_le_ofReal (hnum.trans hmul)
  rw [ENNReal.ofReal_mul
    (FreshSign.rate_nonneg (by norm_num [nonceBits, idxBits, numCuts, trials, idxCost, blockCost, signBudget, msgBits, blockBits]) _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _)
      (add_nonneg (by norm_num) (Nat.cast_nonneg _)))] at h
  have he : ∀ i : Fin numCuts,
      ENNReal.ofReal (((S.samePattern i).card : ℝ) / (64 + (S.samePattern i).card)) =
        AveragedSearch.hitRate (S.samePattern i).card := by
    intro i
    rw [ENNReal.ofReal_div_of_pos (add_pos_of_pos_of_nonneg (by norm_num) (Nat.cast_nonneg _)),
      ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 64) (Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, AveragedSearch.hitRate]
  simpa only [he, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 28),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h

end OptimalOTS.AveragedCounting
