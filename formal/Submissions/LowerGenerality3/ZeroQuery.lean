import Submissions.LowerGenerality3.Costs
import VCVio.EvalDist.Expectation

/-! Zero-cost generic verification is independent of the random-oracle cache. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

abbrev Cache := (hashSpec).QueryCache
abbrev run {α : Type} (oa : OracleComp Spec α) (c : Cache) :
    ProbComp (α × Cache) := (simulateQ (oracleImpl) oa).run c
abbrev E {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞) := expectedValue p f

/-- Keep private randomness and replace every hash answer by zero. -/
def freeImpl : QueryImpl Spec ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) +
    (show QueryImpl (hashSpec) ProbComp from fun _ => pure (0 : BitVec hashBits))

def freeRun {α : Type} (oa : OracleComp Spec α) : ProbComp α :=
  simulateQ (freeImpl) oa

theorem run_pure {α : Type} (x : α) (c : Cache) :
    run (pure x) c = pure (x, c) := by simp [run]

theorem run_bind {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (c : Cache) :
    run (oa >>= k) c = run oa c >>= fun p => run (k p.1) p.2 := by
  simp only [run, simulateQ_bind, StateT.run_bind]

/-- A zero-cost program never hashes, so its output is independent of the unchanged cache. -/
theorem run_zero {α : Type} (oa : OracleComp Spec α)
    (h : CostAtMost oa 0) (c : Cache) :
    run oa c = (fun x => (x, c)) <$> freeRun oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [run_pure, freeRun]
  | query_bind t k ih =>
    unfold CostAtMost at h
    rw [isQueryBound_query_bind_iff] at h
    have hb := h
    cases t with
    | inr q =>
      have hcost := hb.1
      change blockCost q.1 ≤ 0 at hcost
      unfold blockCost at hcost
      omega
    | inl t =>
      have hk : ∀ u, CostAtMost (k u) 0 := by
        intro u
        simpa [CostAtMost, queryCost] using hb.2 u
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have hl : (oracleImpl (.inl t)).run c =
          HasQuery.query (spec := unifSpec) (m := ProbComp) t >>= fun u => pure (u, c) := by
        simp [oracleImpl, StateT.run_monadLift]
      rw [hl]
      simp only [bind_assoc, pure_bind]
      simp only [freeRun, simulateQ_bind, simulateQ_spec_query, freeImpl, QueryImpl.add_apply_inl]
      rw [map_bind]
      congr 1
      funext u
      exact ih u (hk u)

abbrev win (oa : OracleComp Spec Bool) (c : Cache) : ℝ≥0∞ :=
  Pr[= true | Prod.fst <$> run oa c]

theorem probTrue_eq_win (oa : OracleComp Spec Bool) :
    probTrue oa = win oa ∅ := by simp [probTrue, win, run, StateT.run'_eq]

theorem win_bind {α : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec Bool) (c : Cache) :
    win (oa >>= k) c = E (run oa c) (fun x => win (k x.1) x.2) := by
  rw [win, run_bind, map_bind, probOutput_bind_eq_expectedValue]

theorem win_pure (b : Bool) (c : Cache) :
    win (pure b) c = if b then 1 else 0 := by
  cases b <;> simp [win, run_pure]

theorem win_zero (oa : OracleComp Spec Bool)
    (h : CostAtMost oa 0) (c : Cache) :
    win oa c = Pr[= true | freeRun oa] := by
  rw [win, run_zero oa h]
  simp

theorem E_const {α : Type} (p : ProbComp α) (v : ℝ≥0∞) : E p (fun _ => v) = v :=
  expectedValue_const (by simp) v

theorem E_eq_zero_on_support {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞)
    (h : E p f = 0) {x : α} (hx : x ∈ support p) : f x = 0 := by
  have ht : Pr[= x | p] * f x = 0 := (ENNReal.tsum_eq_zero.mp h) x
  exact (mul_eq_zero.mp ht).resolve_left ((probOutput_pos_iff p x).mpr hx).ne'

end OptimalOTS.LowerGenerality3
