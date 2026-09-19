import Submissions.UpperCompressions.IUB

/-!
# The supermartingale master lemma

Let `Φ` be a potential on caches that grows on average by at most `κ · cost q` at every fresh
hash query `q` (a *charge* of `κ` per compression), and let `I c b` be an invariant of the
cache and the remaining budget.  If every continuation `k x` started from a cache `d` with
budget `b'` is bounded by `Φ d + κ b'`, then the whole computation `oa >>= k` started from `c`
with budget `b` is bounded by `Φ c + κ b`:

```
E[Fv x d | (x, d) ← run oa c] ≤ Φ c + κ b.
```

Query bounds are the pathwise `CostAtMost` of `OptimalOTS.Dag`; the continuation's
budget is whatever is left on the path.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem costAtMost_query_bind_iff {α : Type} (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (b : ℕ) :
    CostAtMost (liftM (Spec.query t) >>= k) b ↔
      queryCost t ≤ b ∧ ∀ u, CostAtMost (k u) (b - queryCost t) := by
  unfold CostAtMost
  rw [isQueryBound_query_bind_iff]

theorem sum_inv_card_mul {n : ℕ} (a : ℝ≥0∞) :
    ∑ _x : BitVec n, (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem kappa_split (κ : ℝ≥0∞) {c b : ℕ} (h : c ≤ b) : κ * c + κ * ((b - c : ℕ) : ℝ≥0∞) = κ * b := by
  rw [← mul_add, ← Nat.cast_add, Nat.add_sub_cancel' h]

/-- **Master lemma.** -/
theorem master {α β : Type} (κ : ℝ≥0∞) (Φ : Cache → ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hΦ : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u) ≤
        Φ c + κ * queryCost (.inr q))
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (Fv : α → Cache → ℝ≥0∞)
    (hF : ∀ x d b', I d b' → CostAtMost (k x) b' → Fv x d ≤ Φ d + κ * b') :
    ∀ (c : Cache) (b : ℕ), I c b → CostAtMost (oa >>= k) b →
      E (run oa c) (fun p => Fv p.1 p.2) ≤ Φ c + κ * b := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c b hI hB
    rw [pure_bind] at hB
    rw [run_pure, E_pure]
    exact hF x c b hI hB
  | query_bind t k' ih =>
    intro c b hI hB
    rw [bind_assoc, costAtMost_query_bind_iff] at hB
    obtain ⟨hcost, hB⟩ := hB
    rw [run_query_bind, E_bind]
    rcases t with t | q
    · rw [oracleImpl_run_inl, E_bind]
      refine (expectedValue_le_of_le _ fun u => ?_)
      rw [E_pure]
      have := ih u c b hI (hB u)
      simpa [queryCost] using this
    · rcases hcq : c q with _ | v
      · rw [oracleImpl_run_inr_none hcq, E_bind, E_uniform]
        calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
              E (pure (u, c.cacheQuery q u)) (fun p => E (run (k' p.1) p.2) fun p => Fv p.1 p.2)
            ≤ ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
                (Φ (c.cacheQuery q u) + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞)) := by
              refine Finset.sum_le_sum fun u _ => ?_
              rw [E_pure]
              dsimp only
              gcongr
              exact ih u _ _ (hI_fresh c b q hI hcq hcost u) (hB u)
          _ = (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u)) +
                κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) := by
              simp only [mul_add, Finset.sum_add_distrib, sum_inv_card_mul]
          _ ≤ Φ c + κ * queryCost (.inr q) + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) :=
              add_le_add_left (hΦ c b q hI hcq hcost) _
          _ = Φ c + κ * b := by rw [add_assoc, kappa_split κ hcost]
      · rw [oracleImpl_run_inr_some hcq, E_pure]
        have hsome : (c q).isSome := by simp [hcq]
        calc E (run (k' v) c) (fun p => Fv p.1 p.2)
            ≤ Φ c + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) :=
              ih v c _ (hI_cached c b q hI hsome hcost) (hB v)
          _ ≤ Φ c + κ * b := by
              gcongr
              exact Nat.sub_le _ _

/-- The master lemma without a continuation. -/
theorem master_single {α : Type} (κ : ℝ≥0∞) (Φ : Cache → ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hΦ : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u) ≤
        Φ c + κ * queryCost (.inr q))
    (oa : OracleComp Spec α) (Fv : α → Cache → ℝ≥0∞)
    (hF : ∀ x d, Fv x d ≤ Φ d) :
    ∀ (c : Cache) (b : ℕ), I c b → CostAtMost oa b →
      E (run oa c) (fun p => Fv p.1 p.2) ≤ Φ c + κ * b := by
  intro c b hI hB
  have := master κ Φ I hI_fresh hI_cached hΦ oa pure Fv
    (fun x d b' _ _ => (hF x d).trans le_self_add) c b hI (by rwa [bind_pure])
  exact this

end OptimalOTS

namespace OptimalOTS

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- **Master lemma, for a family of continuations.** The continuation may depend on an index
`j` (in the application: the hidden part of the key), as long as every member of the family
respects the budget. -/
theorem master_family {α β J : Type} [Nonempty J] (κ : ℝ≥0∞) (Φ : Cache → ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hΦ : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u) ≤
        Φ c + κ * queryCost (.inr q))
    (oa : OracleComp Spec α) (k : J → α → OracleComp Spec β) (Fv : α → Cache → ℝ≥0∞)
    (hF : ∀ x d b', I d b' → (∀ j, CostAtMost (k j x) b') → Fv x d ≤ Φ d + κ * b') :
    ∀ (c : Cache) (b : ℕ), I c b → (∀ j, CostAtMost (oa >>= k j) b) →
      E (run oa c) (fun p => Fv p.1 p.2) ≤ Φ c + κ * b := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c b hI hB
    rw [run_pure, E_pure]
    exact hF x c b hI fun j => by simpa [pure_bind] using hB j
  | query_bind t k' ih =>
    intro c b hI hB
    have hcost : queryCost t ≤ b := by
      have := hB (Classical.arbitrary J)
      rw [bind_assoc, costAtMost_query_bind_iff] at this
      exact this.1
    have hB' : ∀ u j, CostAtMost (k' u >>= k j) (b - queryCost t) := fun u j => by
      have := hB j
      rw [bind_assoc, costAtMost_query_bind_iff] at this
      exact this.2 u
    rw [run_query_bind, E_bind]
    rcases t with t | q
    · rw [oracleImpl_run_inl, E_bind]
      refine (expectedValue_le_of_le _ fun u => ?_)
      rw [E_pure]
      have := ih u c b hI (hB' u)
      simpa [queryCost] using this
    · rcases hcq : c q with _ | v
      · rw [oracleImpl_run_inr_none hcq, E_bind, E_uniform]
        calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
              E (pure (u, c.cacheQuery q u)) (fun p => E (run (k' p.1) p.2) fun p => Fv p.1 p.2)
            ≤ ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
                (Φ (c.cacheQuery q u) + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞)) := by
              refine Finset.sum_le_sum fun u _ => ?_
              rw [E_pure]
              dsimp only
              gcongr
              exact ih u _ _ (hI_fresh c b q hI hcq hcost u) (hB' u)
          _ = (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u)) +
                κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) := by
              simp only [mul_add, Finset.sum_add_distrib, sum_inv_card_mul]
          _ ≤ Φ c + κ * queryCost (.inr q) + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) :=
              add_le_add_left (hΦ c b q hI hcq hcost) _
          _ = Φ c + κ * b := by rw [add_assoc, kappa_split κ hcost]
      · rw [oracleImpl_run_inr_some hcq, E_pure]
        have hsome : (c q).isSome := by simp [hcq]
        calc E (run (k' v) c) (fun p => Fv p.1 p.2)
            ≤ Φ c + κ * ((b - queryCost (.inr q) : ℕ) : ℝ≥0∞) :=
              ih v c _ (hI_cached c b q hI hsome hcost) (hB' v)
          _ ≤ Φ c + κ * b := by
              gcongr
              exact Nat.sub_le _ _

end OptimalOTS
