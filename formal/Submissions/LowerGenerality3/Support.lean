import Submissions.LowerGenerality3.Answers

/-!
# Support of a cache, and cost-free private sampling

A computation of cost `b` adds at most `b` entries to the cache (`exists_support_run`), and a
lifted `ProbComp` has cost zero (`costAtMost_liftM`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits securityBits maxSignatureBits keygenBudget signBudget

/-- `D` contains every query for which the cache already has an answer. -/
def HasSupport (c : Cache) (D : Finset Query) : Prop :=
  ∀ q, (c q).isSome → q ∈ D


theorem HasSupport.cacheQuery {c : Cache} {D : Finset Query}
    (hc : HasSupport c D) (q : Query) (u : BitVec hashBits) :
    HasSupport (c.cacheQuery q u) (insert q D) := by
  intro q' hq'
  by_cases h : q' = q
  · simp [h]
  · rw [QueryCache.cacheQuery_of_ne _ _ h] at hq'
    exact Finset.mem_insert_of_mem (hc q' hq')


theorem hasSupport_empty : HasSupport (∅ : Cache) ∅ := by
  intro q hq
  simp at hq


/-- A computation of cost at most `b` adds at most `b` cache entries. -/
theorem exists_support_run {α : Type} (oa : OracleComp Spec α) :
    ∀ {b : ℕ}, CostAtMost oa b → ∀ {c : Cache} {D : Finset Query},
      HasSupport c D → ∀ p ∈ support (run oa c),
        ∃ D' : Finset Query, HasSupport p.2 D' ∧ D'.card ≤ D.card + b := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro b hb c D hc p hp
    rw [run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨D, hc, Nat.le_add_right _ _⟩
  | query_bind t k ih =>
    intro b hb c D hc p hp
    rw [CostAtMost, isQueryBound_query_bind_iff] at hb
    obtain ⟨ht, hk⟩ := hb
    rw [run_query_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
    rcases t with t | q
    · rw [oracleImpl_run_inl, support_bind] at hu
      simp only [Set.mem_iUnion] at hu
      obtain ⟨w, _, hw⟩ := hu
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      simpa only [queryCost, Nat.sub_zero] using ih u (hk u) hc p hp
    · have hqcost : 1 ≤ queryCost (.inr q) := Nat.le_max_left _ _
      rcases hcache : c q with _ | v
      · rw [oracleImpl_run_inr_none hcache, support_bind] at hu
        simp only [Set.mem_iUnion] at hu
        obtain ⟨w, _, hw⟩ := hu
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨D', hD', hcard⟩ := ih u (hk u) (hc.cacheQuery q u) p hp
        refine ⟨D', hD', ?_⟩
        have hins : (insert q D).card ≤ D.card + 1 := Finset.card_insert_le _ _
        omega
      · rw [oracleImpl_run_inr_some hcache, support_pure] at hu
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        obtain ⟨D', hD', hcard⟩ := ih u (hk u) hc p hp
        exact ⟨D', hD', hcard.trans (Nat.add_le_add_left (Nat.sub_le _ _) _)⟩

/-- In particular a run from the empty cache has at most its cost in entries. -/
theorem exists_support_run_empty {α : Type} {oa : OracleComp Spec α}
    {b : ℕ} (hb : CostAtMost oa b) (p : α × Cache)
    (hp : p ∈ support (run oa ∅)) :
    ∃ D : Finset Query, HasSupport p.2 D ∧ D.card ≤ b := by
  simpa only [Finset.card_empty, Nat.zero_add] using
    exists_support_run oa hb (hasSupport_empty) p hp


/-- Private sampling costs nothing. -/
theorem costAtMost_liftM {α : Type} (pc : ProbComp α) : CostAtMost (liftM pc : OracleComp Spec α) 0 := by
  change CostAtMost (liftComp pc Spec) 0
  induction pc using OracleComp.inductionOn with
  | pure x => simp [liftComp]; trivial
  | query_bind t mx ih =>
    rw [liftComp_bind]
    have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) Spec =
        (liftM (Spec.query (.inl t)) : OracleComp Spec _) := by
      simp [liftComp]; rfl
    rw [hq]
    unfold CostAtMost
    rw [isQueryBound_query_bind_iff]
    exact ⟨le_rfl, fun u => by simpa [CostAtMost, queryCost] using ih u⟩

theorem succ_ne (m : Message) : m + 1 ≠ m := by
  intro h
  have h2 : (m + 1 : Message) - m = 1 := by
    rw [BitVec.add_comm]
    exact BitVec.add_sub_cancel 1 m
  rw [h, BitVec.sub_self] at h2
  exact absurd h2 (by decide)

end OptimalOTS.LowerGenerality3
