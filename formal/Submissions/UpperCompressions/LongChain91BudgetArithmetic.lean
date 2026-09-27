import Submissions.UpperCompressions.LongChain91SecurityData
import Submissions.UpperCompressions.LongChain91CachedRow

/-!
# Exact budget arithmetic for the cost-91 long-chain proof

The execution modules feed this file nonnegative clocks and scalar payoff
bounds.  Everything below is deterministic real arithmetic: it records the
common drift rate, the post-sign rate, and the exact coefficients used by the
small- and large-budget endpoints.
-/

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91BudgetArithmetic

open scoped BigOperators

abbrev kappa : ℝ := Chain18Compact.kappa

/-- Common empirical-kernel envelope. -/
def C : ℝ := 99 / 98

/-- Authentication followed by the completed-row excess payoff. -/
def postRate : ℝ := kappa / 2 + C * ((471 / 1000) * kappa)

theorem kappa_pos : 0 < kappa := by
  unfold kappa Chain18Compact.kappa
  positivity

theorem C_nonneg : 0 ≤ C := by norm_num [C]

theorem postRate_nonneg : 0 ≤ postRate := by
  unfold postRate
  exact add_nonneg (div_nonneg kappa_pos.le (by norm_num))
    (mul_nonneg C_nonneg (mul_nonneg (by norm_num) kappa_pos.le))

/-- The exact coefficient produced by the small-game kernel envelope, its
`65/64` stopping factor, the certified mean, and two `1/1000` allowances. -/
theorem small_coefficient_identity (K : ℝ) :
    C * (65 / 64) * (967 / 1000) * kappa * K +
        2 * (kappa * K / 1000) =
      (6235189 / 6272000) * kappa * K := by
  unfold C
  ring

end OptimalOTS.WeightedConstruction.LongChain91BudgetArithmetic
