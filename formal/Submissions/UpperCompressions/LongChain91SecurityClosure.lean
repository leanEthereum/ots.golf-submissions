import Submissions.UpperCompressions.LongChain91Scheme
import Submissions.UpperCompressions.ProofBundle13

/-!
# Security endpoints for the cost-88 long-chain construction

This module isolates the final, exact security closure from the two
construction-specific actual-game estimates.  In particular, it proves the
positive-budget fact from the concrete key-generation cost, transports the
typed experiment across the canonical wire adapter, and closes every budget
once the small- and large-budget estimates below are supplied.
-/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace OptimalOTS.WeightedConstruction.LongChain91BudgetEndpoints

open OracleComp ENNReal
open LongChain91 WeightedReference

/-- Every typed adversarial experiment pays the concrete graph key-generation
cost before running the adversary. -/
theorem experiment_budget (A : typed.Adversary) (B : ℕ)
    (hB : CostAtMost (typed.experiment A) B) : 820 ≤ B := by
  have h := GraphKeygenBridge.costAtMost_keygen_bind
    scheme.graph scheme.publicKey _ hB
  rw [scheme_keygenCost] at h
  exact h.1

/-- The small-budget coefficient is strictly below the target coefficient. -/
theorem small_strict (K : ℝ) (hK : 0 < K) :
    (6235189 : ℝ) / 6272000 * kappa * K < kappa * K := by
  have hk : 0 < kappa * K := mul_pos (by norm_num [kappa]) hK
  nlinarith

/-- The large-budget coefficient is strictly below the target coefficient. -/
theorem large_strict (K : ℝ) (hK : 0 < K) :
    (2423 : ℝ) / 2450 * kappa * K < kappa * K := by
  have hk : 0 < kappa * K := mul_pos (by norm_num [kappa]) hK
  nlinarith

/-- Above the inverse security rate, the trivial probability bound is already
strictly smaller than the target. -/
theorem above_trivial_budget (p : ℝ) (hp : p ≤ 1) (B : ℕ) (hB : 2 ^ 127 < B) :
    p < kappa * (B : ℝ) := by
  have hBr : (2 : ℝ) ^ 127 < B := by exact_mod_cast hB
  have hk := mul_lt_mul_of_pos_left hBr (show 0 < kappa by norm_num [kappa])
  have he : kappa * (2 : ℝ) ^ 127 = 1 := by norm_num [kappa]
  rw [he] at hk
  exact hp.trans_lt hk

/-- Canonical wire encoding transfers typed strong security exactly. -/
theorem raw_secure_of_typed (h : typed.Secure) : wireScheme.Secure :=
  WireAdapter.secure typed decodeWire decodeWire_encode wire_canonical h

end OptimalOTS.WeightedConstruction.LongChain91BudgetEndpoints

namespace OptimalOTS.WeightedConstruction.LongChain91SecurityClosure

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
open LongChain91 LongChain91BudgetEndpoints WeightedReference

/-- Indicator payoff for a successful Boolean experiment. -/
def successValue (b : Bool) : ℝ≥0∞ := if b then 1 else 0

theorem successValue_le_one (b : Bool) : successValue b ≤ 1 := by
  cases b <;> simp [successValue]

/-- The actual-game estimate required on budgets at or below the row threshold. -/
def SmallActualGameBound : Prop :=
  ∀ (A : typed.Adversary) (B : ℕ),
    CostAtMost (typed.experiment A) B →
    (B : ℝ) ≤ (2 : ℝ) ^ 86 / 64 →
    B ≤ 2 ^ 127 →
    E (run (typed.experiment A) ∅) (fun x => successValue x.1) ≤
      ENNReal.ofReal ((6235189 : ℝ) / 6272000 * kappa * (B : ℝ))

/-- The actual-game estimate required from the row threshold through the
inverse security-rate endpoint. -/
def LargeActualGameBound : Prop :=
  ∀ (A : typed.Adversary) (B : ℕ),
    CostAtMost (typed.experiment A) B →
    (2 : ℝ) ^ 86 / 64 ≤ (B : ℝ) →
    B ≤ 2 ^ 127 →
    E (run (typed.experiment A) ∅) (fun x => successValue x.1) ≤
      ENNReal.ofReal ((2423 : ℝ) / 2450 * kappa * (B : ℝ))

theorem probTrue_eq_success (oa : OracleComp Spec Bool) :
    probTrue oa = E (run oa ∅) (fun x => successValue x.1) := by
  unfold probTrue
  rw [run'_eq, probOutput_map_eq_tsum_ite, E, expectedValue_def]
  refine tsum_congr fun x => ?_
  rcases x with ⟨b, c⟩
  cases b <;> simp [successValue]

theorem security_rate (B : ℕ) :
    ENNReal.ofReal (kappa * (B : ℝ)) = (B : ℝ≥0∞) / 2 ^ securityBits := by
  rw [ENNReal.ofReal_mul (by norm_num [kappa])]
  norm_num [kappa, securityBits, ENNReal.ofReal_div_of_pos]
  simp only [div_eq_mul_inv, mul_comm]

/-- The two explicit actual-game bounds imply typed strong security for every
natural budget, including both branch endpoints.  Above `2^127`, the universal
success-probability bound closes the goal strictly. -/
theorem typed_secure_of_bounds
    (small : SmallActualGameBound)
    (large : LargeActualGameBound) : typed.Secure := by
  intro A B hB
  have hbudget : 820 ≤ B := experiment_budget A B hB
  have hpos : 0 < (B : ℝ) := by
    exact_mod_cast (show 0 < B by omega)
  have hrate : 0 < kappa * (B : ℝ) :=
    mul_pos (by norm_num [kappa]) hpos
  rw [probTrue_eq_success, ← security_rate]
  by_cases hcap : B ≤ 2 ^ 127
  · by_cases hsmall : (B : ℝ) ≤ (2 : ℝ) ^ 86 / 64
    · exact (small A B hB hsmall hcap).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hrate).mpr (small_strict B hpos))
    · exact (large A B hB (le_of_not_ge hsmall) hcap).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hrate).mpr (large_strict B hpos))
  · have ht : (1 : ℝ) < kappa * (B : ℝ) :=
      above_trivial_budget 1 le_rfl B (lt_of_not_ge hcap)
    have he : (1 : ℝ≥0∞) < ENNReal.ofReal (kappa * (B : ℝ)) := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_lt_ofReal_iff hrate).mpr ht
    exact (E_le_one _ (fun x : Bool × Cache => successValue_le_one x.1)).trans_lt he

/-- The conditional final raw theorem: supplying the two named actual-game
bounds produces strong security for the public wire scheme. -/
theorem raw_secure_of_bounds
    (small : SmallActualGameBound)
    (large : LargeActualGameBound) : wireScheme.Secure :=
  raw_secure_of_typed (typed_secure_of_bounds small large)

end OptimalOTS.WeightedConstruction.LongChain91SecurityClosure
