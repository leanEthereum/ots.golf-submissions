import Submissions.UpperCompressions.LongChain91BudgetArithmetic

/-!
# Actual-cache stopped moments for the chain-18 decoder

This module specializes the protected-cache score and pair-score martingales
to the concrete length-342 index domain.  The sharp stopped bound retains its
exact endpoint factor `1 + (B-1)/2^86`; two corollaries record what follows at
the accepted `2^86/10` threshold and at the stronger threshold needed for a
`65/64` endpoint factor.
-/

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91SmallMoments

open OracleSpec OracleComp OracleComp.EvalDist
open WeightedCacheCounts WeightedRow.Weights WeightedRealExecution
open scoped Classical BigOperators ENNReal

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

abbrev M := LongChain91Security.M
abbrev decode : BitVec hashBits → Option (Fin M) :=
  LongChain91Empirical.cacheDecode
abbrev securityWeights := LongChain91Security.securityWeights
abbrev mean : ℝ := securityWeights.mean
abbrev kappa : ℝ := LongChain91BudgetArithmetic.kappa
abbrev C : ℝ := LongChain91BudgetArithmetic.C

def queryCount (c : hashSpec.QueryCache) : ℕ :=
  (seen WideDomains.indexDomain c).card

def counts (c : hashSpec.QueryCache) : Fin M → ℕ :=
  classCounts WideDomains.indexDomain c decode

def score (c : hashSpec.QueryCache) : ℝ :=
  securityWeights.score (counts c)

def pairs (c : hashSpec.QueryCache) : ℝ :=
  securityWeights.pairScore (counts c)

def pairEnvelope (c : hashSpec.QueryCache) : ℝ :=
  score c + 2 * pairs c / (2 : ℝ)^86

theorem mean_nonneg : 0 ≤ mean := by
  unfold mean WeightedRow.Weights.mean
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (securityWeights.p_pos i).le (securityWeights.g_nonneg i)

theorem mean_le_kappa : mean ≤ kappa := by
  calc
    mean ≤ (967 / 1000) * kappa :=
      LongChain91Security.securityWeights_mean
    _ ≤ kappa := by
      have hk := LongChain91BudgetArithmetic.kappa_pos.le
      nlinarith

theorem score_nonneg (c : hashSpec.QueryCache) : 0 ≤ score c := by
  unfold score WeightedRow.Weights.score
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (securityWeights.g_nonneg i)

theorem pairs_nonneg (c : hashSpec.QueryCache) : 0 ≤ pairs c := by
  unfold pairs WeightedRow.Weights.pairScore
  exact Finset.sum_nonneg fun i _ => div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (securityWeights.g_nonneg i))
    (securityWeights.p_pos i).le

theorem pairEnvelope_nonneg (c : hashSpec.QueryCache) :
    0 ≤ pairEnvelope c := by
  unfold pairEnvelope
  exact add_nonneg (score_nonneg c)
    (div_nonneg (mul_nonneg (by norm_num) (pairs_nonneg c)) (by positivity))

/-! ## Fresh index domain and exact stopped moments -/

theorem index_initial (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    queryCount c = 0 ∧ counts c = (fun _ => 0) := by
  have he := WideDomains.fresh_seen_empty c hf
  constructor
  · unfold queryCount
    rw [he, Finset.card_empty]
  · unfold counts classCounts
    rw [he]
    funext i
    simp [WeightedPublicCounts.counts]

/-- All three martingale moments for the real adaptive oracle execution. -/
theorem moments { α : Type } (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    let run := (simulateQ oracleImpl oa).run c
    realEval run
      (fun out => score out.2 - mean * (queryCount out.2 : ℝ)) = 0 ∧
    realEval run
      (fun out => pairs out.2 - (queryCount out.2 : ℝ) * score out.2 +
        mean * (queryCount out.2 : ℝ) *
          ((queryCount out.2 : ℝ) + 1) / 2) = 0 ∧
    realEval run
      (fun out => (score out.2 - mean * (queryCount out.2 : ℝ))^2) ≤
        (B : ℝ) *
          ((Chain18Compact.L : ℝ) * kappa / 2) * mean := by
  obtain ⟨hq, hk⟩ := index_initial c hf
  exact WeightedProtectedCache.stopped_moments securityWeights
    WideDomains.indexDomain decode LongChain91Empirical.cache_decoder_law
    ((Chain18Compact.L : ℝ) * kappa / 2)
    (by
      exact div_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          LongChain91BudgetArithmetic.kappa_pos.le) (by norm_num))
    LongChain91Security.referenceWeight_le oa B hB c hq hk

theorem realEval_congr_support { α : Type } (oa : ProbComp α)
    (f g : α → ℝ) (
      h : ∀ a ∈ support oa, f a = g a) :
    realEval oa f = realEval oa g :=
  le_antisymm
    (realEval_mono_of_support oa f g (fun a ha => (h a ha).le))
    (realEval_mono_of_support oa g f (fun a ha => (h a ha).symm.le))

theorem queryCount_le_budget_on_support { α : Type }
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none)
    (out : α × hashSpec.QueryCache)
    (hout : out ∈ support ((simulateQ oracleImpl oa).run c)) :
    queryCount out.2 ≤ B := by
  have h := WeightedProtectedCache.count_bound WideDomains.indexDomain
    oa B hB c out hout
  have hq := (index_initial c hf).1
  change queryCount out.2 ≤
    min WideDomains.indexDomain.card (queryCount c + B) at h
  rw [hq, zero_add] at h
  exact h.trans (min_le_right _ _)

/-! ## Sharp and rounded stopped payoffs -/

/-- The exact endpoint factor furnished by the generic stopped theorem.
Only the covariance term uses the `B ≤ 2^86/10` hypothesis. -/
theorem sharp_stopped_payoff_actual { α : Type }
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 10)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) (d : ℝ) :
    realEval ((simulateQ oracleImpl oa).run c) (fun out =>
      C * pairEnvelope out.2 +
        d * ((B : ℝ) - (queryCount out.2 : ℝ))) ≤
      (B : ℝ) * max d
        (C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86)) +
          kappa * (B : ℝ) / 1000 := by
  let run := (simulateQ oracleImpl oa).run c
  let τ : α × hashSpec.QueryCache → ℝ := fun out =>
    min (queryCount out.2 : ℝ) (B : ℝ)
  have hτ (out) (ho : out ∈ support run) :
      τ out = (queryCount out.2 : ℝ) := by
    exact min_eq_left (by
      exact_mod_cast queryCount_le_budget_on_support oa B hB c hf out ho)
  obtain ⟨hm1, hm2, hmSq⟩ := moments oa B hB c hf
  have hm1' : realEval run (fun out => score out.2 - mean * τ out) = 0 := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hm1
  have hm2' : realEval run (fun out =>
      pairs out.2 - τ out * score out.2 +
        mean * τ out * (τ out + 1) / 2) = 0 := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hm2
  have hmSq' : realEval run
      (fun out => (score out.2 - mean * τ out)^2) ≤
        (B : ℝ) * ((Chain18Compact.L : ℝ) * kappa / 2) * mean := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hmSq
  have hK : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
  have hG : 0 ≤ (Chain18Compact.L : ℝ) * kappa / 2 :=
    div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        LongChain91BudgetArithmetic.kappa_pos.le) (by norm_num)
  have hT : 0 < kappa * (2 : ℝ)^86 / 4096 := by
    exact div_pos
      (mul_pos LongChain91BudgetArithmetic.kappa_pos (by positivity))
      (by norm_num)
  have hgmax :
      (Chain18Compact.L : ℝ) * kappa / 2 ≤ (2 : ℝ)^20 * kappa / 2 := by
    norm_num [Chain18Compact.L]
  have hs := WeightedStopping.stopped_payoff
    (realEval run) (realEval_mono run) (realEval_const run 1)
    τ (fun out => score out.2) (fun out => pairs out.2)
    C mean d ((2 : ℝ)^86) (B : ℝ)
    ((B : ℝ) * ((Chain18Compact.L : ℝ) * kappa / 2) * mean)
    (kappa * (2 : ℝ)^86 / 4096)
    LongChain91BudgetArithmetic.C_nonneg mean_nonneg (by positivity) hK hT
    (fun out => le_min (Nat.cast_nonneg _) (Nat.cast_nonneg B))
    (fun out => min_le_right _ _) hm1' hm2' hmSq'
  have hc := WeightedStopping.mixed72_covariance
    C kappa (B : ℝ) ((Chain18Compact.L : ℝ) * kappa / 2) mean
    LongChain91BudgetArithmetic.C_nonneg
    (by norm_num [C, LongChain91BudgetArithmetic.C])
    LongChain91BudgetArithmetic.kappa_pos hK hG mean_nonneg hBN hgmax
    mean_le_kappa
  have h := hs.trans (add_le_add le_rfl hc)
  rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])] at h
  simpa only [pairEnvelope] using h

theorem factor_65_of_budget64 (B : ℕ)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64) :
    1 + ((B : ℝ) - 1) / (2 : ℝ)^86 ≤ 65 / 64 := by
  have hN : 0 < (2 : ℝ)^86 := by positivity
  have hratio : ((B : ℝ) - 1) / (2 : ℝ)^86 ≤ 1 / 64 :=
    (div_le_iff₀ hN).2 (by linarith)
  linarith

theorem budget64_le_budget10 (B : ℕ)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64) :
    (B : ℝ) ≤ (2 : ℝ)^86 / 10 := by
  have hN : 0 ≤ (2 : ℝ)^86 := by positivity
  nlinarith

/-! ## Real/ENNReal transport -/

theorem hazard_le_pairEnvelope (m : Message) (c : hashSpec.QueryCache) :
    securityWeights.hazard ((2 : ℝ)^86)
      (seen (WideDomains.rowDomain m) c).card
      (classCounts WideDomains.indexDomain c decode)
      (classCounts (WideDomains.rowDomain m) c decode) ≤ pairEnvelope c := by
  apply securityWeights.hazard_le_score_pair _ (by positivity) _ _ _
  intro i
  exact WeightedCacheCounts.classCounts_mono
    (WideDomains.row_subset m) c decode i

end OptimalOTS.WeightedConstruction.LongChain91SmallMoments
