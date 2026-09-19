import Submissions.LowerGenerality1.Cache
import VCVio.EvalDist.Expectation

/-! Generic expectation identities for the bare-oracle lower-bound analysis. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


/-- Expected value of `g` over a probabilistic computation. -/
abbrev E {α : Type} (p : ProbComp α) (g : α → ℝ≥0∞) : ℝ≥0∞ := expectedValue p g

theorem E_bind {α β : Type} (p : ProbComp α) (k : α → ProbComp β) (g : β → ℝ≥0∞) :
    E (p >>= k) g = E p fun x => E (k x) g :=
  expectedValue_bind p k g

theorem E_pure {α : Type} (x : α) (g : α → ℝ≥0∞) : E (pure x) g = g x :=
  expectedValue_pure x g

theorem E_mono {α : Type} (p : ProbComp α) {g h : α → ℝ≥0∞} (hgh : ∀ x, g x ≤ h x) :
    E p g ≤ E p h :=
  expectedValue_mono p hgh

theorem E_map {α β : Type} (p : ProbComp α) (f : α → β) (g : β → ℝ≥0∞) :
    E (f <$> p) g = E p fun x => g (f x) :=
  expectedValue_map p f g

theorem E_uniform (n : ℕ) (g : BitVec n → ℝ≥0∞) :
    E ($ᵗ BitVec n) g = ∑ x, (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * g x := by
  rw [E, expectedValue_def, tsum_fintype]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [probOutput_uniformSample]

end OptimalOTS
