import Submissions.UpperCompressions.LongChain91SmallSecurity
import Submissions.UpperCompressions.LongChain91LargeSecurity
import Submissions.UpperCompressions.LongChain91SecurityClosure

/-!
# Strong security of the cost-91 long-chain construction

The concrete small- and large-budget estimates use the actual Boolean-game
payoff.  This module identifies that payoff with the endpoint indicator and
supplies both branches to the common typed and wire security closures.
-/

noncomputable section

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

namespace OptimalOTS.WeightedConstruction.LongChain91Secure

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] hashBits blockBits msgBits Finset.univ Finset.filter

/-- The schedule and generic endpoint modules use the same inverse security
rate, with inverse and division notation respectively. -/
private theorem kappa_eq_reference :
    LongChain91BudgetArithmetic.kappa = WeightedReference.kappa := by
  norm_num [LongChain91BudgetArithmetic.kappa, Chain18Compact.kappa,
    WeightedReference.kappa]

/-- The concrete small-budget theorem has exactly the payoff and coefficient
required by the common endpoint closure. -/
theorem smallActualGameBound :
    LongChain91SecurityClosure.SmallActualGameBound := by
  intro A B hB hsmall hcap
  have hcapReal : (B : ℝ) ≤ (2 : ℝ) ^ 127 := by
    exact_mod_cast hcap
  have h := LongChain91SmallSecurity.actual_small_security
    A hB hsmall hcapReal
  have hpay : LongChain91.successValue =
      (fun x : Bool × OptimalOTS.Cache =>
        LongChain91SecurityClosure.successValue x.1) := by
    funext x
    rcases x with ⟨b, c⟩
    cases b <;> simp [LongChain91.successValue,
      LongChain91SecurityClosure.successValue]
  rw [hpay] at h
  rw [← kappa_eq_reference]
  exact h

/-- The concrete large-budget theorem has exactly the payoff and coefficient
required by the common endpoint closure. -/
theorem largeActualGameBound :
    LongChain91SecurityClosure.LargeActualGameBound := by
  intro A B hB hlarge hcap
  have hcapReal : (B : ℝ) ≤ (2 : ℝ) ^ 127 := by
    exact_mod_cast hcap
  have h := LongChain91LargeSecurity.actual_large_security
    A hB hlarge hcapReal
  have hpay : LongChain91.successValue =
      (fun x : Bool × OptimalOTS.Cache =>
        LongChain91SecurityClosure.successValue x.1) := by
    funext x
    rcases x with ⟨b, c⟩
    cases b <;> simp [LongChain91.successValue,
      LongChain91SecurityClosure.successValue]
  rw [hpay] at h
  rw [← kappa_eq_reference]
  exact h

/-- Strong security of the canonical public wire encoding. -/
theorem raw_secure : LongChain91.wireScheme.Secure :=
  LongChain91SecurityClosure.raw_secure_of_bounds
    smallActualGameBound largeActualGameBound

end OptimalOTS.WeightedConstruction.LongChain91Secure
