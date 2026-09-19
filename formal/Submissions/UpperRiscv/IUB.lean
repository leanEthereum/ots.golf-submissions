import Submissions.UpperRiscv.Cache
import VCVio.EvalDist.Expectation

/-!
# Identical until bad

Running a computation from the cache `extend c f` (the entries of `f` are answered from `f`) is
bounded by running it from `c` alone (the same points get fresh answers), where every run that
ever queries a point of `f` is charged in full:

```
E[φ | run oa (extend c f)] ≤ E[fun (x, d) => if Hits d f then 1 else φ (x, extend d f) | run oa c]
```

for `φ ≤ 1` and `c` disjoint from `f`.  The two runs agree until the first query at a point of
`f`; from then on the right-hand side pays `1`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


/-- Expected value of `g` over a probabilistic computation. -/
abbrev E {α : Type} (p : ProbComp α) (g : α → ℝ≥0∞) : ℝ≥0∞ := expectedValue p g

theorem E_le_one {α : Type} (p : ProbComp α) {g : α → ℝ≥0∞} (hg : ∀ x, g x ≤ 1) : E p g ≤ 1 :=
  (expectedValue_le_of_le p hg).trans (by simp)

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

theorem E_const_le {α : Type} (p : ProbComp α) (c : ℝ≥0∞) : E p (fun _ => c) ≤ c :=
  expectedValue_le_of_le p fun _ => le_rfl

theorem E_uniform (n : ℕ) (g : BitVec n → ℝ≥0∞) :
    E ($ᵗ BitVec n) g = ∑ x, (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * g x := by
  rw [E, expectedValue_def, tsum_fintype]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [probOutput_uniformSample]

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- **Identical until bad.** -/
theorem iub {α : Type} (oa : OracleComp Spec α) (f : Cache)
    (φ : α × Cache → ℝ≥0∞) (hφ : ∀ p, φ p ≤ 1) :
    ∀ c : Cache, Cache.Disjoint c f →
      E (run oa (Cache.extend c f)) φ ≤
        E (run oa c) fun p => if Cache.Hits p.2 f then 1 else φ (p.1, Cache.extend p.2 f) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c hc
    rw [run_pure, run_pure, E_pure, E_pure]
    simp [hc.not_hits]
  | query_bind t k ih =>
    intro c hc
    rw [run_query_bind, run_query_bind, E_bind, E_bind]
    rcases t with t | q
    · rw [oracleImpl_run_inl, oracleImpl_run_inl, E_bind, E_bind]
      refine E_mono _ fun u => ?_
      rw [E_pure, E_pure]
      exact ih u c hc
    · rcases hcq : c q with _ | v
      · rcases hfq : f q with _ | w
        · -- fresh on both sides
          have hcq' : Cache.extend c f q = none := by simp [Cache.extend, hcq, hfq]
          rw [oracleImpl_run_inr_none hcq, oracleImpl_run_inr_none hcq', E_bind, E_bind]
          refine E_mono _ fun u => ?_
          rw [E_pure, E_pure]
          dsimp only
          rw [← Cache.extend_cacheQuery]
          exact ih u _ (Cache.disjoint_cacheQuery hc hfq u)
        · -- the point is in `f`: the real run answers from `f`, the other side pays `1`
          have hcq' : Cache.extend c f q = some w := by simp [Cache.extend, hcq, hfq]
          rw [oracleImpl_run_inr_some hcq', oracleImpl_run_inr_none hcq, E_pure, E_bind]
          have hw : (f q).isSome := by simp [hfq]
          calc E (run (k w) (Cache.extend c f)) φ ≤ 1 := E_le_one _ hφ
            _ ≤ E ($ᵗ BitVec hashBits) fun u => E (pure (u, c.cacheQuery q u)) fun p =>
                  E (run (k p.1) p.2) fun p =>
                    if Cache.Hits p.2 f then 1 else φ (p.1, Cache.extend p.2 f) := by
                rw [E_uniform]
                have h1 : ∀ u : BitVec hashBits, E (pure (u, c.cacheQuery q u)) (fun p =>
                    E (run (k p.1) p.2) fun p =>
                      if Cache.Hits p.2 f then 1 else φ (p.1, Cache.extend p.2 f)) = 1 := by
                  intro u
                  rw [E_pure]
                  have hsub : ∀ p ∈ support (run (k u) (c.cacheQuery q u)),
                      Cache.Hits p.2 f := fun p hp =>
                    ⟨q, hw, (sub_of_mem_support_run _ _ p hp).isSome (by simp)⟩
                  have : E (run (k u) (c.cacheQuery q u)) (fun p =>
                      if Cache.Hits p.2 f then 1 else φ (p.1, Cache.extend p.2 f)) =
                      E (run (k u) (c.cacheQuery q u)) (fun _ => 1) := by
                    refine expectedValue_congr_of_support fun p hp => ?_
                    rw [if_pos (hsub p hp)]
                  rw [this, E, expectedValue_const (by simp)]
                simp only [h1, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
                rw [ENNReal.mul_inv_cancel (by simp) (by simp)]
      · -- cached on both sides
        have hcq' : Cache.extend c f q = some v := by simp [Cache.extend, hcq]
        rw [oracleImpl_run_inr_some hcq, oracleImpl_run_inr_some hcq', E_pure, E_pure]
        exact ih v c hc

end OptimalOTS
