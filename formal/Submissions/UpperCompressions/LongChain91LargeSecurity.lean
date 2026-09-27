import Submissions.UpperCompressions.LongChain91PayoffExpansion
import Submissions.UpperCompressions.LongChain91LargeTerminal
import Submissions.UpperCompressions.LongChain91SecurityClosure
import Submissions.UpperCompressions.ProofBundle13

/-!
# Large-budget actual-game closure for the cost-90 long chain

The good replay hazard, authentication work, and post-sign continuation share
the same public query clock.  The terminal large-row theorem supplies the four
`2^-244` concentration tails and the all-row `2^-334` occupancy tail; completed
row failures contribute `(1+B) * 2^-760` once after averaging.
-/

noncomputable section

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators

namespace OptimalOTS.WeightedConstruction.LongChain91LargeSecurity

open LongChain91 LongChain91InitialGame WeightedReplacement WeightedReference
open WideDomains WeightedCacheCounts
open LongChain91LargeTerminal LongChain91TailArithmetic

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

abbrev kappa : ℝ := LongChain91BudgetArithmetic.kappa
abbrev C : ℝ := LongChain91BudgetArithmetic.C
abbrev postRate : ℝ := LongChain91BudgetArithmetic.postRate
abbrev tightAlpha : ℝ := LongChain91CollisionArithmetic.tightAlpha
abbrev N : ℝ := LongChain91CollisionArithmetic.N

variable (A : scheme.toAlgorithm.Adversary)

/-! ## Exact shared-clock scalar closure -/

/-- A form of the checked real scalar closure in which the replay term has
already been multiplied by the empirical kernel constant `C`. -/
theorem large_scalar_closure_scaled (K q a t H : ℝ)
    (hq : 0 ≤ q) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hclock : q + a + t ≤ K)
    (hH : H ≤ C * tightAlpha * q + C * (kappa * K / 100)) :
    (kappa / 2) * a + H + postRate * t + kappa * K / 1000 ≤
      (2423 / 2450) * kappa * K := by
  have hC : 0 < C := by
    norm_num [C, LongChain91BudgetArithmetic.C]
  have hraw : H / C ≤ tightAlpha * q + kappa * K / 100 := by
    apply (div_le_iff₀ hC).2
    calc
      H ≤ C * tightAlpha * q + C * (kappa * K / 100) := hH
      _ = (tightAlpha * q + kappa * K / 100) * C := by ring
  have h := LongChain91CollisionArithmetic.large_scalar_closure_tight
    K q a t (H / C) hq ha ht hclock hraw
  have heq : C * (H / C) = H := by
    field_simp [hC.ne']
  rw [heq] at h
  linarith

/-- ENNReal realization of the same shared-clock allocation.  `r` is the
already-kernel-scaled replay clock. -/
theorem large_shared_ennreal (B : ℕ) (q a t r e : ℝ≥0∞)
    (hclock : q + a + t ≤ B)
    (hr : r ≤ ENNReal.ofReal (C * tightAlpha) * q +
      ENNReal.ofReal (C * (kappa * (B : ℝ) / 100)))
    (he : e ≤ ENNReal.ofReal (kappa * (B : ℝ) / 1000)) :
    ENNReal.ofReal (kappa / 2) * a + r +
        ENNReal.ofReal postRate * t + e ≤
      ENNReal.ofReal ((2423 / 2450) * kappa * (B : ℝ)) := by
  have hrate : 0 ≤ C * tightAlpha :=
    mul_nonneg LongChain91BudgetArithmetic.C_nonneg
      LongChain91CollisionArithmetic.tightAlpha_nonneg
  have hshift : 0 ≤ C * (kappa * (B : ℝ) / 100) := by
    exact mul_nonneg LongChain91BudgetArithmetic.C_nonneg
      (div_nonneg (mul_nonneg LongChain91BudgetArithmetic.kappa_pos.le
        (Nat.cast_nonneg B)) (by norm_num))
  have herr : 0 ≤ kappa * (B : ℝ) / 1000 := by
    exact div_nonneg
      (mul_nonneg LongChain91BudgetArithmetic.kappa_pos.le
        (Nat.cast_nonneg B)) (by norm_num)
  have haRate : ENNReal.ofReal (kappa / 2) ≤
      ENNReal.ofReal (C * tightAlpha) :=
    ENNReal.ofReal_le_ofReal
      LongChain91CollisionArithmetic.authRate_le_C_tightAlpha
  have htRate : ENNReal.ofReal postRate ≤
      ENNReal.ofReal (C * tightAlpha) :=
    ENNReal.ofReal_le_ofReal
      LongChain91CollisionArithmetic.postRate_le_C_tightAlpha
  calc
    _ ≤ ENNReal.ofReal (C * tightAlpha) * a +
        (ENNReal.ofReal (C * tightAlpha) * q +
          ENNReal.ofReal (C * (kappa * (B : ℝ) / 100))) +
        ENNReal.ofReal (C * tightAlpha) * t +
          ENNReal.ofReal (kappa * (B : ℝ) / 1000) :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul' haRate le_rfl) hr) (mul_le_mul' htRate le_rfl)) he
    _ = ENNReal.ofReal (C * tightAlpha) * (q + a + t) +
        ENNReal.ofReal (C * (kappa * (B : ℝ) / 100)) +
          ENNReal.ofReal (kappa * (B : ℝ) / 1000) := by ring
    _ ≤ ENNReal.ofReal (C * tightAlpha) * B +
        ENNReal.ofReal (C * (kappa * (B : ℝ) / 100)) +
          ENNReal.ofReal (kappa * (B : ℝ) / 1000) :=
      add_le_add (add_le_add (mul_le_mul' le_rfl hclock) le_rfl) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_natCast B, ← ENNReal.ofReal_mul hrate,
        ← ENNReal.ofReal_add
          (mul_nonneg hrate (Nat.cast_nonneg B)) hshift,
        ← ENNReal.ofReal_add
          (add_nonneg (mul_nonneg hrate (Nat.cast_nonneg B)) hshift) herr]
      congr 1
      exact LongChain91CollisionArithmetic.large_coefficient_tight_identity
        (B : ℝ)

/-! ## Actual public clocks -/

def largeGood (B : ℕ) (_pk : PublicKey)
    (r : (Message × A.State) × Cache × ℕ) : Prop :=
  LongChain91LargeTerminal.LargeGood B r.2.1

def countClock (_pk : PublicKey)
    (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  LongChain91SmallMoments.queryCount r.2.1

def preOther : ℝ≥0∞ :=
  ∑ pk : PublicKey, sumW (fiberA pk) *
    expectedCharge (otherPaid (isIndexLength (msgBits + 86))) (A.choose pk) ∅

theorem preAuth_eq :
    preAuth A = ENNReal.ofReal (kappa / 2) * preOther A := by
  unfold preAuth preOther
  rw [LongChain91Continuation.authRate_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem choose_budget {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (pk : PublicKey) : CostAtMost (A.choose pk) B :=
  OptimalOTS.AlgorithmCosts.CostAtMost.mono
    (choose_reserved_budget A hB pk).2
    ((Nat.sub_le _ _).trans (Nat.sub_le _ _))

theorem choose_count_other_post_le {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B) (pk : PublicKey) :
    E (runRemaining (A.choose pk) ∅ (B - 1087)) (countClock A pk) +
      expectedCharge (otherPaid (isIndexLength (msgBits + 86)))
        (A.choose pk) ∅ +
      E (runRemaining (A.choose pk) ∅ (B - 1087))
        (postRemaining A pk) ≤ B := by
  have hd := distinct_other_le_expected_paid (A.choose pk) ∅
    (fun _ _ => rfl)
  rw [← runRemaining_project (A.choose pk) ∅ (B - 1087), E_map] at hd
  have hh := (add_le_add hd (le_refl
    (E (runRemaining (A.choose pk) ∅ (B - 1087))
      (postRemaining A pk)))).trans
      (choose_spent_post_remaining_le A hB pk)
  exact hh.trans (by
    exact_mod_cast
      ((Nat.sub_le (B - 1087) signBudget).trans (Nat.sub_le B 1087)))

theorem global_count_other_post_le {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B) :
    weightedClock A B (countClock A) + preOther A +
      weightedClock A B (postRemaining A) ≤ B := by
  unfold weightedClock preOther
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk) * (B : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro pk _
      simpa only [mul_add] using mul_le_mul'
        (le_refl (sumW (fiberA pk))) (choose_count_other_post_le A hB pk)
    _ = _ := by rw [← Finset.sum_mul, sum_fiber_weights, one_mul]

/-! ## Terminal failure and good-hazard aggregation -/

theorem large_bad_clock_le {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (hlarge : N / 64 ≤ (B : ℝ)) :
    weightedClock A B (badGate A (largeGood A B)) ≤
      4 * LongChain91LargeTerminal.eps244 +
        (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  have htail (pk : PublicKey) :
      E (runRemaining (A.choose pk) ∅ (B - 1087))
          (badGate A (largeGood A B) pk) ≤
        4 * LongChain91LargeTerminal.eps244 +
          (2 : ℝ≥0∞)⁻¹ ^ 334 := by
    have hb := choose_budget A hB pk
    have h := LongChain91LargeTerminal.actual_large_good_failure_bound
      B hlarge (A.choose pk) hb ∅ (fun _ _ => rfl)
    have he : E (run (A.choose pk) ∅)
        (fun p => if ¬ LongChain91LargeTerminal.LargeGood B p.2
          then 1 else 0) =
        Pr[fun p => ¬ LongChain91LargeTerminal.LargeGood B p.2 |
          run (A.choose pk) ∅] := expectedValue_ite_one _ _
    rw [← he, ← runRemaining_project (A.choose pk) ∅ (B - 1087), E_map] at h
    convert h using 1
    congr 1
    funext r
    unfold badGate largeGood
    by_cases hg : LongChain91LargeTerminal.LargeGood B r.2.1 <;>
      simp only [hg, not_true_eq_false, not_false_eq_true, if_true, if_false]
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk) *
        (4 * LongChain91LargeTerminal.eps244 +
          (2 : ℝ≥0∞)⁻¹ ^ 334) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (htail pk)
    _ = _ := by rw [← Finset.sum_mul, sum_fiber_weights, one_mul]

theorem large_hazard_clock_le (B : ℕ) :
    weightedClock A B (gatedHazard A (largeGood A B)) ≤
      ENNReal.ofReal (C * tightAlpha) * weightedClock A B (countClock A) +
        ENNReal.ofReal (C * (kappa * (B : ℝ) / 100)) := by
  have hpoint (pk : PublicKey)
      (r : (Message × A.State) × Cache × ℕ) :
      gatedHazard A (largeGood A B) pk r ≤
        ENNReal.ofReal (C * tightAlpha) * countClock A pk r +
          ENNReal.ofReal (C * (kappa * (B : ℝ) / 100)) := by
    by_cases hg : largeGood A B pk r
    · rw [gatedHazard, if_pos hg]
      have hh : LongChain91LargeHazard.hazard r.1.1 r.2.1 <
          tightAlpha *
              (LongChain91LargeHazard.globalCount r.2.1 : ℝ) +
            LongChain91CollisionArithmetic.largeDeviation (B : ℝ) :=
        lt_of_not_ge (fun h => hg.2 ⟨r.1.1, h⟩)
      have hc : 0 ≤ C := LongChain91BudgetArithmetic.C_nonneg
      have hreal : C * cacheHazard r.1.1 r.2.1 ≤
          C * (tightAlpha *
              (LongChain91LargeHazard.globalCount r.2.1 : ℝ) +
            LongChain91CollisionArithmetic.largeDeviation (B : ℝ)) := by
        change C * LongChain91LargeHazard.hazard r.1.1 r.2.1 ≤ _
        exact mul_le_mul_of_nonneg_left hh.le hc
      have h := ENNReal.ofReal_le_ofReal hreal
      apply h.trans_eq
      have hrate : 0 ≤ C * tightAlpha :=
        mul_nonneg hc LongChain91CollisionArithmetic.tightAlpha_nonneg
      have hshift : 0 ≤ C * (kappa * (B : ℝ) / 100) := by
        exact mul_nonneg LongChain91BudgetArithmetic.C_nonneg
          (div_nonneg
            (mul_nonneg LongChain91BudgetArithmetic.kappa_pos.le
              (Nat.cast_nonneg B))
            (by norm_num))
      rw [show C * (tightAlpha *
            (LongChain91LargeHazard.globalCount r.2.1 : ℝ) +
          LongChain91CollisionArithmetic.largeDeviation (B : ℝ)) =
          (C * tightAlpha) *
              (LongChain91LargeHazard.globalCount r.2.1 : ℝ) +
            C * (kappa * (B : ℝ) / 100) by
          unfold LongChain91CollisionArithmetic.largeDeviation
          ring,
        ENNReal.ofReal_add (mul_nonneg hrate (Nat.cast_nonneg _)) hshift,
        ENNReal.ofReal_mul hrate, ENNReal.ofReal_natCast]
      rfl
    · rw [gatedHazard, if_neg hg]
      exact zero_le
  calc
    _ ≤ weightedClock A B (fun pk r =>
        ENNReal.ofReal (C * tightAlpha) * countClock A pk r +
          ENNReal.ofReal (C * (kappa * (B : ℝ) / 100))) :=
      Finset.sum_le_sum fun pk _ =>
        mul_le_mul' le_rfl (E_mono _ (hpoint pk))
    _ = ENNReal.ofReal (C * tightAlpha) * weightedClock A B (countClock A) +
        weightedClock A B (fun _ _ =>
          ENNReal.ofReal (C * (kappa * (B : ℝ) / 100))) := by
      rw [weightedClock_add, weightedClock_const_mul]
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ ∑ pk : PublicKey, sumW (fiberA pk) *
            ENNReal.ofReal (C * (kappa * (B : ℝ) / 100)) :=
          Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (E_const_le _ _)
        _ = _ := by rw [← Finset.sum_mul, sum_fiber_weights, one_mul]

/-! ## Negligible-tail closure -/

theorem ofReal_inv_two_pow (n : ℕ) :
    ENNReal.ofReal (((2 : ℝ)^n)⁻¹) = (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)^n),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  simpa only [ENNReal.inv_pow]

theorem large_exception_margin_ennreal (B : ℕ)
    (hlarge : N / 64 ≤ (B : ℝ))
    (hcap : (B : ℝ) ≤ (2 : ℝ)^127) :
    4 * LongChain91LargeTerminal.eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334 +
        (1 + (B : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 760 ≤
      ENNReal.ofReal (kappa * (B : ℝ) / 1000) := by
  have h := ENNReal.ofReal_le_ofReal
    (LongChain91CollisionArithmetic.large_exception_margin
      (B : ℝ) hlarge hcap)
  have hlhs :
      ENNReal.ofReal
        (4 * ((2 : ℝ)^244)⁻¹ + ((2 : ℝ)^334)⁻¹ +
          (1 + (B : ℝ)) * ((2 : ℝ)^760)⁻¹) =
        4 * LongChain91LargeTerminal.eps244 +
          (2 : ℝ≥0∞)⁻¹ ^ 334 +
          (1 + (B : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 760 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one,
      ofReal_inv_two_pow, ofReal_inv_two_pow, ofReal_inv_two_pow]
    unfold LongChain91LargeTerminal.eps244
    rw [ofReal_inv_two_pow]
    norm_num only [ENNReal.ofReal_ofNat]
  rw [hlhs] at h
  exact h

/-! ## Final actual-game theorem -/

theorem actual_large_security {B : ℕ}
    (hB : CostAtMost (scheme.toAlgorithm.experiment A) B)
    (hBN : (2 : ℝ)^86 / 64 ≤ (B : ℝ))
    (hcap : (B : ℝ) ≤ (2 : ℝ)^127) :
    E (run (scheme.toAlgorithm.experiment A) ∅) successValue ≤
      ENNReal.ofReal ((2423 / 2450) * kappa * (B : ℝ)) := by
  have hlarge : N / 64 ≤ (B : ℝ) := by
    simpa only [N, LongChain91CollisionArithmetic.N] using hBN
  have hex := global_actual_payoff_expanded A hB (largeGood A B)
    (fun _ _ h => h.1)
  have hbad := large_bad_clock_le A hB hlarge
  have hh := large_hazard_clock_le A B
  have he := large_exception_margin_ennreal B hlarge hcap
  have herr : weightedClock A B (badGate A (largeGood A B)) +
      (1 + (B : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 760 ≤
        ENNReal.ofReal (kappa * (B : ℝ) / 1000) :=
    (add_le_add hbad le_rfl).trans he
  rw [preAuth_eq A] at hex
  have hn := large_shared_ennreal B
    (weightedClock A B (countClock A)) (preOther A)
    (weightedClock A B (postRemaining A))
    (weightedClock A B (gatedHazard A (largeGood A B)))
    (weightedClock A B (badGate A (largeGood A B)) +
      (1 + (B : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 760)
    (global_count_other_post_le A hB) hh herr
  exact hex.trans (by simpa only [add_assoc] using hn)

#print axioms large_scalar_closure_scaled
#print axioms large_shared_ennreal
#print axioms global_count_other_post_le
#print axioms large_bad_clock_le
#print axioms large_hazard_clock_le
#print axioms large_exception_margin_ennreal
#print axioms actual_large_security

end OptimalOTS.WeightedConstruction.LongChain91LargeSecurity
