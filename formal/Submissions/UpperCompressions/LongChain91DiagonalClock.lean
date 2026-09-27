import Submissions.UpperCompressions.LongChain91CollisionArithmetic
import Submissions.UpperCompressions.LongChain91SmallMoments

/-!
# Global diagonal-clock concentration for the cost-91 decoder

The equality replay variance uses `D + X` on one message row and `Qfwd` on
the global index domain.  Both deterministic clocks are dominated by the
single global diagonal score `Dglobal`.  Reweighting the accepted decoder
classes by their collision masses turns this score into an ordinary protected
cache score, so the accepted time-uniform score MGF gives a direct actual-cache
tail at `3/2` times its certified mean rate.
-/

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91DiagonalClock

open OracleSpec OracleComp OracleComp.EvalDist
open WeightedCacheCounts WeightedRow.Weights
open scoped Classical BigOperators ENNReal

open LongChain91Security LongChain91CollisionArithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev M := LongChain91Security.M
abbrev decode := LongChain91Empirical.cacheDecode
abbrev securityWeights := LongChain91Security.securityWeights
abbrev kappa : ℝ := Chain18Compact.kappa

abbrev globalCount (c : hashSpec.QueryCache) : ℕ :=
  LongChain91SmallMoments.queryCount c

abbrev globalCounts (c : hashSpec.QueryCache) : Fin M → ℕ :=
  LongChain91SmallMoments.counts c

/-- The diagonal score accumulated by every distinct public index query. -/
def Dglobal (c : hashSpec.QueryCache) : ℝ :=
  securityWeights.D (globalCounts c)

/-- The same diagonal score restricted to one nonce row. -/
def Drow (m : Message) (c : hashSpec.QueryCache) : ℝ :=
  securityWeights.D
    (classCounts (WideDomains.rowDomain m) c decode)

/-- Decoder weights reweighted by the collision mass.  The decoder law is
unchanged, while its score is exactly `Dglobal`. -/
def collisionWeights : WeightedRow.Weights (Fin M) :=
  securityWeights.withScore securityWeights.collisionMass
    securityWeights.collisionMass_nonneg

/-- Pointwise bound for one diagonal increment. -/
def diagonalJump : ℝ :=
  (13 / 40) * (Chain18Compact.L : ℝ)^2 * kappa

/-- Exponential parameter used by the global score boundary. -/
def diagonalTheta : ℝ := 1 / (3 * diagonalJump)

/-- Half of the certified diagonal mean rate. -/
def diagonalDelta : ℝ := diagonalRate / 2

theorem diagonalJump_pos : 0 < diagonalJump := by
  unfold diagonalJump
  have hL : 0 < (Chain18Compact.L : ℝ) := by
    norm_num [Chain18Compact.L]
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hL))
    LongChain91BudgetArithmetic.kappa_pos

theorem diagonalTheta_pos : 0 < diagonalTheta := by
  unfold diagonalTheta
  exact one_div_pos.mpr (mul_pos (by norm_num) diagonalJump_pos)

theorem diagonalDelta_pos : 0 < diagonalDelta := by
  unfold diagonalDelta
  exact div_pos diagonalRate_pos (by norm_num)

/-! ## Reweighted-score identities -/

theorem collisionWeights_mean :
    collisionWeights.mean = securityWeights.diagonalMean := by
  unfold collisionWeights WeightedRow.Weights.withScore WeightedRow.Weights.mean
    WeightedRow.Weights.diagonalMean WeightedRow.Weights.collisionMass
  apply Finset.sum_congr rfl
  intro i hi
  change securityWeights.p i *
    (securityWeights.g i ^ 2 / securityWeights.p i) =
      securityWeights.g i ^ 2
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ _ (securityWeights.p_pos i).ne'

theorem collisionWeights_mean_nonneg : 0 ≤ collisionWeights.mean := by
  unfold WeightedRow.Weights.mean
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (collisionWeights.p_pos i).le
      (collisionWeights.g_nonneg i)

theorem collisionWeights_mean_lt :
    collisionWeights.mean < diagonalRate := by
  rw [collisionWeights_mean]
  exact LongChain91CollisionArithmetic.diagonalMean_lt

theorem collisionWeights_mean_le :
    collisionWeights.mean ≤ diagonalRate := collisionWeights_mean_lt.le

theorem collisionWeights_g_le (i : Fin M) :
    collisionWeights.g i ≤ diagonalJump := by
  exact (LongChain91CollisionArithmetic.collisionMass_lt i).le

theorem collisionWeights_decoder_law (x : Option (Fin M)) :
    ((Finset.univ.filter fun b : BitVec hashBits => decode b = x).card : ℝ) /
        Fintype.card (BitVec hashBits) = collisionWeights.classMass x := by
  exact (LongChain91Empirical.cache_decoder_law x).trans
    (WeightedRow.Weights.withScore_classMass securityWeights
      securityWeights.collisionMass securityWeights.collisionMass_nonneg x).symm

theorem collisionWeights_score (c : hashSpec.QueryCache) :
    collisionWeights.score (globalCounts c) = Dglobal c := by
  rfl

theorem collisionWeights_M1 (c : hashSpec.QueryCache) :
    collisionWeights.M1 (globalCount c) (globalCounts c) =
      Dglobal c - collisionWeights.mean * (globalCount c : ℝ) := by
  unfold WeightedRow.Weights.M1
  rw [collisionWeights_score]

/-! ## Deterministic clock domination -/

theorem Drow_le_Dglobal (m : Message) (c : hashSpec.QueryCache) :
    Drow m c ≤ Dglobal c := by
  unfold Drow Dglobal WeightedRow.Weights.D
  apply Finset.sum_le_sum
  intro i hi
  have hc := WeightedCacheCounts.classCounts_mono
    (WideDomains.row_subset m) c decode i
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
    (securityWeights.collisionMass_nonneg i)

theorem Qfwd_le_Dglobal (c : hashSpec.QueryCache) :
    securityWeights.Qfwd (globalCounts c) ≤ Dglobal c := by
  unfold Dglobal WeightedRow.Weights.Qfwd WeightedRow.Weights.D
  apply Finset.sum_le_sum
  intro i hi
  by_cases hz : globalCounts c i = 0
  · simp [hz]
  · rw [if_neg hz]
    have hone : (1 : ℝ) ≤ (globalCounts c i : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hone
      (securityWeights.collisionMass_nonneg i)

/-! ## Time-uniform actual-cache concentration -/

/-- The score boundary used below.  `max globalCount B` makes the result
time-uniform without assuming a budget inside the stopped-process theorem. -/
def diagonalBoundary (B : ℝ) (c : hashSpec.QueryCache) : Prop :=
  diagonalDelta * max (globalCount c : ℝ) B ≤
    collisionWeights.M1 (globalCount c) (globalCounts c)

theorem diagonal_rate_le :
    WeightedEmpirical.rate collisionWeights diagonalTheta diagonalJump ≤
      diagonalTheta * diagonalDelta / 2 := by
  have hJ := diagonalJump_pos
  have hm := collisionWeights_mean_le
  have hm0 := collisionWeights_mean_nonneg
  have hc := diagonalRate_pos
  have hrate :
      WeightedEmpirical.rate collisionWeights diagonalTheta diagonalJump =
        collisionWeights.mean / (16 * diagonalJump) := by
    unfold WeightedEmpirical.rate diagonalTheta
    field_simp [hJ.ne']
    ring
  have htarget :
      diagonalTheta * diagonalDelta / 2 =
        diagonalRate / (12 * diagonalJump) := by
    unfold diagonalTheta diagonalDelta
    field_simp [hJ.ne']
    ring
  rw [hrate, htarget]
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hJ)
    (mul_pos (by norm_num) hJ)).2
  nlinarith

theorem diagonal_exponent (B : ℝ) (hB : N / 64 ≤ B) :
    (2^56 : ℝ) ≤ diagonalTheta * diagonalDelta * B / 2 := by
  norm_num [diagonalTheta, diagonalDelta, diagonalJump, diagonalRate,
    N, kappa, Chain18Compact.L, Chain18Compact.kappa] at hB ⊢
  linarith

theorem global_diagonal_crossing {α : Type}
    (oa : OracleComp Spec α) (B : ℝ) (hB : N / 64 ≤ B)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    LongChain91Empirical.crossing oa initial (diagonalBoundary B) ≤
      ENNReal.ofReal (Real.exp (-(2^56 : ℝ))) := by
  obtain ⟨hq, hk⟩ := LongChain91SmallMoments.index_initial initial hfresh
  have hx := WeightedActualScore.global_boundary collisionWeights oracleImpl
    globalCount globalCounts
    (WeightedDirectCache.protectedFresh WideDomains.indexDomain)
    (WeightedProtectedCache.query_law collisionWeights
      WideDomains.indexDomain decode collisionWeights_decoder_law)
    false diagonalJump diagonalTheta diagonalDelta B
    diagonalJump_pos.le collisionWeights_g_le diagonalTheta_pos.le
    (by
      unfold diagonalTheta
      have hJ := diagonalJump_pos
      field_simp [hJ.ne']
      norm_num)
    diagonalDelta_pos.le diagonal_rate_le oa initial hq hk
  have he := diagonal_exponent B hB
  have hexp :
      Real.exp (-(diagonalTheta * diagonalDelta * B / 2)) ≤
        Real.exp (-(2^56 : ℝ)) :=
    Real.exp_le_exp.mpr (neg_le_neg he)
  have htail := hx.trans (ENNReal.ofReal_le_ofReal hexp)
  change LongChain91Empirical.crossing oa initial (diagonalBoundary B) ≤ _
    at htail
  exact htail

theorem exp_neg_pow56_le :
    Real.exp (-(2^56 : ℝ)) ≤ ((2 : ℝ)^1024)⁻¹ := by
  have hmono : Real.exp (-(2^56 : ℝ)) ≤ Real.exp (-(1024 : ℝ)) := by
    exact Real.exp_le_exp.mpr (by norm_num)
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ)^1024 ≤ (Real.exp 1)^1024 :=
    pow_le_pow_left₀ (by norm_num) he 1024
  rw [← Real.exp_nat_mul, mul_one] at hp
  have htail : Real.exp (-(1024 : ℝ)) ≤ ((2 : ℝ)^1024)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hp
  exact hmono.trans htail

theorem global_diagonal_crossing_dyadic {α : Type}
    (oa : OracleComp Spec α) (B : ℝ) (hB : N / 64 ≤ B)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    LongChain91Empirical.crossing oa initial (diagonalBoundary B) ≤
      (2 : ℝ≥0∞)⁻¹^1024 := by
  have h := (global_diagonal_crossing oa B hB initial hfresh).trans
    (ENNReal.ofReal_le_ofReal exp_neg_pow56_le)
  rw [ENNReal.ofReal_inv_of_pos
      (by positivity : (0 : ℝ) < (2 : ℝ)^1024),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)] at h
  norm_num only [ENNReal.ofReal_ofNat] at h
  simpa only [ENNReal.inv_pow] using h

/-! ## Terminal consequence under a paid-query budget -/

end OptimalOTS.WeightedConstruction.LongChain91DiagonalClock
