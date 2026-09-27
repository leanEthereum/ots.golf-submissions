import Submissions.UpperCompressions.LongChain91BudgetArithmetic

/-!
# Concrete post-sign continuation for the cost-91 schedule

This file keeps the actual signing loop and public cache visible.  It combines
the cached alternate-class replay bound, the literal post-sign excess bound,
and the authentication rate before the full game averages over public keys.
-/

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91Continuation

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open WeightedReplacement WeightedCompletion WeightedCacheCounts
open scoped Classical BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

abbrev M := LongChain91Security.M
abbrev decode := LongChain91Empirical.cacheDecode
abbrev tier := LongChain91Empirical.rank
abbrev securityWeights := LongChain91Security.securityWeights
abbrev excess := LongChain91Security.excess
abbrev C := LongChain91BudgetArithmetic.C
abbrev kappa := LongChain91BudgetArithmetic.kappa
abbrev postRate := LongChain91BudgetArithmetic.postRate

/-- Replay hazard already exposed in the actual shared cache. -/
def cacheHazard (m : Message) (c : Cache) : ℝ :=
  securityWeights.hazard ((2 : ℝ)^86)
    (seen (WideDomains.rowDomain m) c).card
    (classCounts WideDomains.indexDomain c decode)
    (classCounts (WideDomains.rowDomain m) c decode)

/-- The post-sign excess payoff of a selected nonce/class pair. -/
def excessPayoff : Option (WeightedSampling.Winner 86 M) → ℝ≥0∞ :=
  fun s => ENNReal.ofReal (score s (fun r => excess r.2))

theorem direct_excess_bound (m : Message) (c : Cache)
    (hc : LongChain91Empirical.Good c) :
    outE (WeightedSampling.loop 86 decode tier m Chain18Compact.L) c
        excessPayoff ≤
      ENNReal.ofReal (C * ((471 / 1000 : ℝ) * kappa)) +
        ENNReal.ofReal (LongChain91CachedRow.tableFailure m c) := by
  exact (LongChain91CachedRow.actual_excess_bound m c hc).trans
    ENNReal.ofReal_add_le

theorem authRate_ofReal :
    LongChain91.authRate = ENNReal.ofReal (kappa / 2) := by
  unfold LongChain91.authRate kappa LongChain91BudgetArithmetic.kappa
    Chain18Compact.kappa
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)^127)]
  norm_num

theorem concrete_postRate :
    LongChain91.authRate +
        ENNReal.ofReal (C * ((471 / 1000 : ℝ) * kappa)) =
      ENNReal.ofReal postRate := by
  rw [authRate_ofReal, ← ENNReal.ofReal_add]
  · rfl
  · exact div_nonneg LongChain91BudgetArithmetic.kappa_pos.le (by norm_num)
  · exact mul_nonneg LongChain91BudgetArithmetic.C_nonneg
      (mul_nonneg (by norm_num) LongChain91BudgetArithmetic.kappa_pos.le)

end OptimalOTS.WeightedConstruction.LongChain91Continuation
