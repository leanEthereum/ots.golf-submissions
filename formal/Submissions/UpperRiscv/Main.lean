import Submissions.UpperRiscv.Assembly

/-!
# Security of the concrete scheme

`forestScheme_secure`: the flat forest satisfies `GScheme.Secure`, the
127-bit strong unforgeability requirement of `OptimalOTS.Dag`, and every signature verifies
in `173` compressions (`forestScheme_verifyCost`).

For a budget `B ≤ 2 ^ 127` the bound `probTrue ≤ 2 ε (B - 492) = (B - 492) / 2 ^ 127 < B / 2 ^ 127`
of `Forest.main_bound` applies; for larger budgets the requirement holds trivially since
probabilities are at most one.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

attribute [local irreducible] GScheme.experiment forestScheme

theorem kappa_eq : κ = ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
  unfold κ ε
  rw [show (2 : ℝ≥0∞) ^ 128 = 2 * 2 ^ 127 by rw [← pow_succ']]
  rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem kappa_mul_lt {B : ℕ} (h492 : 492 ≤ B) :
    κ * ((B - 492 : ℕ) : ℝ≥0∞) < (B : ℝ≥0∞) / 2 ^ securityBits := by
  rw [kappa_eq]
  show _ < (B : ℝ≥0∞) / 2 ^ 127
  rw [ENNReal.div_eq_inv_mul]
  refine ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    (ENNReal.inv_ne_top.2 (by simp)) ?_
  exact_mod_cast Nat.sub_lt (by omega) (by norm_num)

theorem one_lt_div {B : ℕ} (h : 2 ^ 127 < B) : (1 : ℝ≥0∞) < (B : ℝ≥0∞) / 2 ^ securityBits := by
  show (1 : ℝ≥0∞) < (B : ℝ≥0∞) / 2 ^ 127
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
  exact_mod_cast h

/-- **Security of the concrete scheme.** -/
theorem forestScheme_secure : forestScheme.Secure := by
  intro A B hB
  by_cases hle : B ≤ 2 ^ 127
  · have h1 := @main_bound A B hB hle
    have h2 := @keygen_le A B hB
    exact h1.trans_lt (kappa_mul_lt h2)
  · exact (probOutput_le_one).trans_lt (one_lt_div (not_le.1 hle))

end Forest

/--
info: 'OptimalOTS.Forest.forestScheme_secure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Forest.forestScheme_secure

/--
info: 'OptimalOTS.Forest.forestScheme_verifyCost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Forest.forestScheme_verifyCost

end OptimalOTS
