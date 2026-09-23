import Submissions.UpperRiscv.Assembly

/-!
# Security of the concrete scheme

`forestScheme_secure`: the bare-chain forest satisfies `GScheme.Secure`, the
127-bit strong unforgeability requirement of `OptimalOTS.Dag`, and every signature verifies
in `205` compressions (`forestScheme_verifyCost`).

For a budget `B ≤ 2 ^ 127` the bound `probTrue ≤ 2 ε (B - 1039) + 2 δ` of `Forest.main_bound`
applies, and `2 δ = 4 · 1025² · 2⁻¹⁶⁰ < 1039 · 2⁻¹²⁷` makes it smaller than `B / 2 ^ 127`; for larger
budgets the requirement holds trivially since probabilities are at most one.
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

/-- The bad records cost less than the keygen budget saves. -/
theorem two_δ_lt : 2 * δ < 1039 * κ := by
  have h0 : (2 : ℝ≥0∞) ^ 33 ≠ 0 := by simp
  have ht : (2 : ℝ≥0∞) ^ 33 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have h0' : ((2 : ℝ≥0∞) ^ 127)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have ht' : ((2 : ℝ≥0∞) ^ 127)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simp)
  have e : ε₁ = ((2 : ℝ≥0∞) ^ 33)⁻¹ * ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
    rw [ε₁, show (2 : ℝ≥0∞) ^ 160 = 2 ^ 33 * 2 ^ 127 by rw [← pow_add],
      ENNReal.mul_inv (Or.inl h0) (Or.inl ht)]
  rw [kappa_eq, δ, e]
  calc 2 * (2 * (1025 * 1025) * (((2 : ℝ≥0∞) ^ 33)⁻¹ * ((2 : ℝ≥0∞) ^ 127)⁻¹))
      = ((2 : ℝ≥0∞) ^ 127)⁻¹ * (2 * (2 * (1025 * 1025)) * ((2 : ℝ≥0∞) ^ 33)⁻¹) := by ring
    _ < ((2 : ℝ≥0∞) ^ 127)⁻¹ * 1039 := by
        refine ENNReal.mul_lt_mul_right h0' ht' ?_
        rw [← div_eq_mul_inv, ENNReal.div_lt_iff (Or.inl h0) (Or.inl ht)]
        exact_mod_cast (by norm_num : (2 * (2 * (1025 * 1025)) : ℕ) < 1039 * 2 ^ 33)
    _ = 1039 * ((2 : ℝ≥0∞) ^ 127)⁻¹ := mul_comm _ _

theorem kappa_mul_lt {B : ℕ} (h1039 : 1039 ≤ B) :
    κ * ((B - 1039 : ℕ) : ℝ≥0∞) + 2 * δ < (B : ℝ≥0∞) / 2 ^ securityBits := by
  have hfin : κ * ((B - 1039 : ℕ) : ℝ≥0∞) ≠ ⊤ := by
    rw [kappa_eq]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by simp)) (ENNReal.natCast_ne_top _)
  calc κ * ((B - 1039 : ℕ) : ℝ≥0∞) + 2 * δ
      < κ * ((B - 1039 : ℕ) : ℝ≥0∞) + 1039 * κ := ENNReal.add_lt_add_left hfin two_δ_lt
    _ = κ * (((B - 1039 : ℕ) : ℝ≥0∞) + 1039) := by ring
    _ = κ * (B : ℝ≥0∞) := by
        congr 1
        exact_mod_cast Nat.sub_add_cancel h1039
    _ = (B : ℝ≥0∞) / 2 ^ securityBits := by
        rw [kappa_eq]
        show _ = (B : ℝ≥0∞) / 2 ^ 127
        rw [ENNReal.div_eq_inv_mul]

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
