import OptimalOTS.Dag

/-!
# Caches of the lazy random oracle

Generic facts about `oracleImpl` (the lazy random oracle of `OptimalOTS.Dag`) used by the
bare-oracle lower-bound analysis:

* `Sub c c'`: every entry of `c` is an entry of `c'`;
* the one-step run lemmas of `oracleImpl`;
* runs only grow the cache (`sub_of_mem_support_run`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- The cache of the random oracle. -/
abbrev Cache := (hashSpec).QueryCache

/-- The lazy random oracle run from cache `c`. -/
abbrev run {α : Type} (oa : OracleComp Spec α) (c : Cache) :
    ProbComp (α × Cache) :=
  (simulateQ (oracleImpl) oa).run c

namespace Cache


/-- Every entry of `c` is an entry of `c'`. -/
def Sub (c c' : Cache) : Prop := ∀ q u, c q = some u → c' q = some u

theorem Sub.refl (c : Cache) : Sub c c := fun _ _ h => h

theorem Sub.trans {c₁ c₂ c₃ : Cache} (h₁ : Sub c₁ c₂) (h₂ : Sub c₂ c₃) : Sub c₁ c₃ :=
  fun q u h => h₂ q u (h₁ q u h)

theorem sub_cacheQuery_of_none {c : Cache} {q : Query} (h : c q = none)
    (u : BitVec hashBits) : Sub c (c.cacheQuery q u) := by
  intro q' u' hq'
  have hne : q' ≠ q := fun e => by rw [e, h] at hq'; cases hq'
  rw [QueryCache.cacheQuery_of_ne _ _ hne]; exact hq'

end Cache

/-! ## One-step run lemmas for the lazy oracle -/

theorem oracleImpl_run_inl (c : Cache) (t : ℕ) :
    (oracleImpl (.inl t)).run c =
      HasQuery.query (spec := unifSpec) (m := ProbComp) t >>= fun u => pure (u, c) := by
  simp [oracleImpl, StateT.run_monadLift]

theorem oracleImpl_run_inr_none {c : Cache} {q : Query} (hc : c q = none) :
    (oracleImpl (.inr q)).run c =
      ($ᵗ BitVec hashBits) >>= fun u => pure (u, c.cacheQuery q u) := by
  have := randomOracle.run_eq (spec₀ := hashSpec) q c
  rw [hc] at this
  exact this

theorem oracleImpl_run_inr_some {c : Cache} {q : Query} {u : BitVec hashBits}
    (hc : c q = some u) : (oracleImpl (.inr q)).run c = pure (u, c) := by
  have := randomOracle.run_eq (spec₀ := hashSpec) q c
  rw [hc] at this
  exact this

theorem run_pure {α : Type} (x : α) (c : Cache) :
    run (pure x) c = pure (x, c) := by
  simp [run]

theorem run_query_bind {α : Type} (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) :
    run (liftM (Spec.query t) >>= k) c =
      (oracleImpl t).run c >>= fun p => run (k p.1) p.2 := by
  simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem run_bind {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (c : Cache) :
    run (oa >>= k) c = run oa c >>= fun p => run (k p.1) p.2 := by
  simp only [run, simulateQ_bind, StateT.run_bind]

theorem run_map {α β : Type} (oa : OracleComp Spec α) (f : α → β)
    (c : Cache) :
    run (f <$> oa) c = (fun p => (f p.1, p.2)) <$> run oa c := by
  simp only [run, simulateQ_map, StateT.run_map]

theorem run'_eq {α : Type} (oa : OracleComp Spec α) (c : Cache) :
    (simulateQ (oracleImpl) oa).run' c = Prod.fst <$> run oa c := by
  simp [run, StateT.run'_eq]

/-- A lifted `ProbComp` runs unchanged and leaves the cache alone. -/
theorem run_liftM {α : Type} (pc : ProbComp α) (c : Cache) :
    run (liftM pc : OracleComp Spec α) c = (fun x => (x, c)) <$> pc := by
  change run (liftComp pc Spec) c = _
  induction pc using OracleComp.inductionOn generalizing c with
  | pure x => simp [liftComp, run_pure]
  | query_bind t mx ih =>
    rw [liftComp_bind]
    have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) Spec =
        (liftM (Spec.query (.inl t)) : OracleComp Spec _) := by
      simp [liftComp]; rfl
    rw [hq, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, ih, map_bind]
    rfl

/-- Runs only grow the cache. -/
theorem sub_of_mem_support_run {α : Type} (oa : OracleComp Spec α) :
    ∀ (c : Cache) (p : α × Cache), p ∈ support (run oa c) → Cache.Sub c p.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c p hp
    rw [run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact Cache.Sub.refl c
  | query_bind t k ih =>
    intro c p hp
    rw [run_query_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
    rcases t with t | q
    · rw [oracleImpl_run_inl, support_bind] at hu
      simp only [Set.mem_iUnion] at hu
      obtain ⟨w, -, hw⟩ := hu
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ih u _ p hp
    · rcases hc : c q with _ | v
      · rw [oracleImpl_run_inr_none hc, support_bind] at hu
        simp only [Set.mem_iUnion] at hu
        obtain ⟨w, -, hw⟩ := hu
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact (Cache.sub_cacheQuery_of_none hc u).trans (ih u _ p hp)
      · rw [oracleImpl_run_inr_some hc, support_pure] at hu
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact ih u _ p hp

end OptimalOTS
