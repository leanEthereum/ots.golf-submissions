import Submissions.LowerGenerality1.CacheFresh
import Submissions.LowerGenerality1.Expectation

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.BareLower

open OptimalOTS.Dag


theorem expectedValue_ge_indicator {α : Type} (p : ProbComp α)
    (good : α → Prop) (g : α → ℝ≥0∞) (a : ℝ≥0∞)
    (hg : ∀ x ∈ support p, good x → a ≤ g x) :
    E p (fun x => if good x then (1 : ℝ≥0∞) else 0) * a ≤ E p g := by
  rw [← expectedValue_mul_const]
  apply expectedValue_mono_of_support
  intro x hx
  by_cases h : good x
  · simpa only [if_pos h, one_mul] using hg x hx h
  · simp only [if_neg h, zero_mul, zero_le]

/-- Freshness bounds with a one-percent slack, used by the averaged attack. -/
theorem ninety_nine_hundredths : (1 - 1 / 100 : ℝ≥0∞) = 99 / 100 := by
  calc
    (1 - 1 / 100 : ℝ≥0∞) = ENNReal.ofReal ((1 : ℝ) - 1 / 100) := by
      rw [ENNReal.ofReal_sub _ (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    _ = _ := by norm_num [ENNReal.ofReal_div_of_pos]

theorem fresh_mass_paper_99 {c : Cache} {D : Finset Query}
    (hc : HasSupport c D) (hD : D.card ≤ 2 ^ 22) :
    (99 / 100 : ℝ≥0∞) ≤ E ($ᵗ BitVec msgBits)
      (fun m => if FreshMessage c m then 1 else 0) := by
  have hb := uniform_nonfresh_le hc
  have hb' : E ($ᵗ BitVec msgBits)
      (fun m => if ¬ FreshMessage c m then (1 : ℝ≥0∞) else 0) ≤ 1 / 100 := by
    apply hb.trans
    calc (D.card : ℝ≥0∞) / 2 ^ msgBits
        ≤ ((2 ^ 22 : ℕ) : ℝ≥0∞) / 2 ^ msgBits :=
          ENNReal.div_le_div_right (by exact_mod_cast hD) _
      _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_div, hashBits, blockBits, pkBits, msgBits, securityBits, maxSignatureBits, keygenBudget, signBudget]
  have h := uniform_complement_ge msgBits (fun m => ¬ FreshMessage c m) _ hb'
  simpa only [not_not, ninety_nine_hundredths] using h

theorem fresh_new_mass_paper_99 {c : Cache} {D : Finset Query}
    (hc : HasSupport c D) (hD : D.card ≤ 2 ^ 22) (m₁ : Message) :
    (99 / 100 : ℝ≥0∞) ≤ E ($ᵗ BitVec msgBits)
      (fun m => if FreshMessage c m ∧ m ≠ m₁ then 1 else 0) := by
  have h := uniform_fresh_ne_ge hc m₁
  apply le_trans _ h
  have hb : ((D.card + 1 : ℕ) : ℝ≥0∞) / 2 ^ msgBits ≤ 1 / 100 := by
    calc ((D.card + 1 : ℕ) : ℝ≥0∞) / 2 ^ msgBits
        ≤ ((2 ^ 22 + 1 : ℕ) : ℝ≥0∞) / 2 ^ msgBits :=
          ENNReal.div_le_div_right (by exact_mod_cast Nat.add_le_add_right hD 1) _
      _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_div, hashBits, blockBits, pkBits, msgBits, securityBits, maxSignatureBits, keygenBudget, signBudget]
  calc (99 / 100 : ℝ≥0∞) = 1 - 1 / 100 := ninety_nine_hundredths.symm
    _ ≤ _ := tsub_le_tsub_left hb 1


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem probTrue_eq_expectation (oa : OracleComp Spec Bool) :
    probTrue oa = E (run oa ∅) (fun p => if p.1 = true then 1 else 0) := by
  unfold probTrue
  rw [run'_eq, ← probEvent_eq_eq_probOutput, probEvent_map]
  exact (expectedValue_ite_one _ _).symm

end OptimalOTS.BareLower
