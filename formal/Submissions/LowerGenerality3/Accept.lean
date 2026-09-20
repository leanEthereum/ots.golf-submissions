import Submissions.LowerGenerality3.OneQuery
import Submissions.LowerGenerality3.CacheLemmas

/-!
# Acceptance of a shape from a cache

`win` of a constant is the constant; of a one-query shape at a cached point, the decision on
the cached answer; at an uncached point, the acceptance rate over a uniform answer. Acceptance
with probability one at an uncached point forces every answer to be accepted (`all_of_rate_one`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

theorem win_const (b : Bool) (c : Cache) : win (Shape.const b).comp c = if b then 1 else 0 :=
  win_pure b c

theorem run_query (t : Spec.Domain) (c : Cache) :
    run (liftM (Spec.query t) : OracleComp Spec _) c = (oracleImpl t).run c := by
  simp only [run, simulateQ_spec_query]

theorem win_one_some {c : Cache} {q : Query} {y : BitVec hashBits} (hc : c q = some y)
    (f : BitVec hashBits → Bool) : win (Shape.one q f).comp c = if f y then 1 else 0 := by
  show win (liftM (Spec.query (.inr q)) >>= fun y => pure (f y)) c = _
  rw [win, run_bind, run_query, oracleImpl_run_inr_some hc]
  simp [run_pure]

/-- The acceptance rate of `f` over a uniform answer. -/
def rate (f : BitVec hashBits → Bool) : ℝ≥0∞ := Pr[= true | f <$> ($ᵗ BitVec hashBits : ProbComp _)]

theorem win_one_none {c : Cache} {q : Query} (hc : c q = none)
    (f : BitVec hashBits → Bool) : win (Shape.one q f).comp c = rate f := by
  show win (liftM (Spec.query (.inr q)) >>= fun y => pure (f y)) c = _
  rw [win, run_bind, run_query, oracleImpl_run_inr_none hc, rate]
  simp only [bind_assoc, pure_bind, run_pure, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- A rate of one means every answer is accepted. -/
theorem all_of_rate_one {f : BitVec hashBits → Bool} (h : rate f = 1) : ∀ y, f y = true := by
  intro y
  by_contra hy
  have hall := ((probOutput_eq_one_iff_forall _ _).mp h).2
  have hmem : false ∈ support (f <$> ($ᵗ BitVec hashBits : ProbComp _)) := by
    rw [support_map]
    exact ⟨y, by simp, by simpa using hy⟩
  exact Bool.false_ne_true (hall false hmem)

end OptimalOTS.LowerGenerality3
