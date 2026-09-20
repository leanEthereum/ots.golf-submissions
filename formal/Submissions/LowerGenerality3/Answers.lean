import Submissions.LowerGenerality3.Martingale

/-!
# Querying a list and collecting the answers

`answers l` queries every member of `l` and returns the pairs `(q, answer)`. Every returned pair
is in the final cache, every member of `l` is returned, and the computation costs at most the
length of `l` when its members are short.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

/-- Query every member of a list and collect the answers. -/
def answers : List Query → OracleComp Spec (List (Query × BitVec hashBits))
  | [] => pure []
  | q :: l => (liftM (Spec.query (.inr q)) : OracleComp Spec (BitVec hashBits)) >>= fun y =>
      (fun r => (q, y) :: r) <$> answers l

/-- Every returned pair is an entry of the final cache, and every member of the list is returned. -/
theorem answers_spec (l : List Query) :
    ∀ (c : Cache) (p : List (Query × BitVec hashBits) × Cache), p ∈ support (run (answers l) c) →
      (∀ e ∈ p.1, p.2 e.1 = some e.2) ∧ (∀ q ∈ l, ∃ y, (q, y) ∈ p.1) := by
  induction l with
  | nil =>
    intro c p hp
    simp only [answers, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨fun e he => absurd he List.not_mem_nil, fun q hq => absurd hq List.not_mem_nil⟩
  | cons q₀ l ih =>
    intro c p hp
    simp only [answers] at hp
    rw [run_bind, run_query, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
    rw [run_map, support_map] at hp
    obtain ⟨⟨r, c''⟩, hr, hp⟩ := hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    have hsub : Cache.Sub c' c'' := sub_of_mem_support_run _ _ _ hr
    have hc' : c' q₀ = some u := by
      rcases hc : c q₀ with _ | v
      · rw [oracleImpl_run_inr_none hc, support_bind] at hu
        simp only [Set.mem_iUnion] at hu
        obtain ⟨w, -, hw⟩ := hu
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact QueryCache.cacheQuery_self _ _ _
      · rw [oracleImpl_run_inr_some hc, support_pure] at hu
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact hc
    obtain ⟨h1, h2⟩ := ih c' (r, c'') hr
    refine ⟨fun e he => ?_, fun q hq => ?_⟩
    · rcases List.mem_cons.mp he with rfl | he'
      · exact hsub _ _ hc'
      · exact h1 e he'
    · rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨u, List.mem_cons_self⟩
      · obtain ⟨y, hy⟩ := h2 q hq'
        exact ⟨y, List.mem_cons_of_mem _ hy⟩

theorem cost_answers (l : List Query) (hl : ∀ q ∈ l, q.1 ≤ 512) :
    CostAtMost (answers l) l.length := by
  induction l with
  | nil => trivial
  | cons q₀ l ih =>
    have hq := hl q₀ List.mem_cons_self
    have hrest := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    simp only [answers, List.length_cons]
    unfold CostAtMost
    rw [isQueryBound_query_bind_iff]
    have hb : blockCost q₀.1 = 1 := by unfold blockCost blockBits; omega
    refine ⟨?_, fun _ => ?_⟩
    · change blockCost q₀.1 ≤ l.length + 1
      omega
    · change ((fun r => (q₀, _) :: r) <$> answers l).IsQueryBound (l.length + 1 - blockCost q₀.1) _ _
      rw [hb, Nat.add_sub_cancel]
      exact Costs.CostAtMost.map hrest _

/-- Every member of a list containing `Q` is cached after `answers l`, so `Q` is decided with
probability exactly `1 − Sm`. -/
theorem E_dec_answers (c₀ : Cache) (P : Query → BitVec hashBits → Prop) (Q : Finset Query)
    (l : List Query) (hQ : ∀ q ∈ Q, q ∈ l) :
    E (run (answers l) c₀) (fun p => if Dec c₀ P Q p.2 then 1 else 0) = 1 - Sm c₀ P Q c₀ := by
  have h := E_Sm_run c₀ P Q (answers l) c₀
  have hcached : ∀ p ∈ support (run (answers l) c₀), ∀ q ∈ Q, (p.2 q).isSome := by
    intro p hp q hq
    obtain ⟨h1, h2⟩ := answers_spec l c₀ p hp
    obtain ⟨y, hy⟩ := h2 q (hQ q hq)
    rw [h1 (q, y) hy]; rfl
  have hS : E (run (answers l) c₀) (fun p => Sm c₀ P Q p.2) =
      E (run (answers l) c₀) (fun p => if Dec c₀ P Q p.2 then 0 else 1) := by
    apply le_antisymm
    · apply expectedValue_mono_of_support
      intro p hp
      rw [Sm_eq_of_cached c₀ P Q (hcached p hp)]
    · apply expectedValue_mono_of_support
      intro p hp
      rw [Sm_eq_of_cached c₀ P Q (hcached p hp)]
  have hsum : E (run (answers l) c₀) (fun p => if Dec c₀ P Q p.2 then 0 else 1) +
      E (run (answers l) c₀) (fun p => if Dec c₀ P Q p.2 then 1 else 0) = 1 := by
    rw [← expectedValue_add]
    calc _ = E (run (answers l) c₀) (fun _ => (1 : ℝ≥0∞)) := by
          apply congrArg; funext p; split_ifs <;> simp
      _ = 1 := E_const _ _
  rw [← hS, h] at hsum
  exact (ENNReal.eq_sub_of_add_eq (by
    rw [Sm]; split_ifs
    · exact ENNReal.zero_ne_top
    · exact (ENNReal.prod_lt_top (fun q _ => tsub_le_self.trans_lt ENNReal.one_lt_top)).ne)
    (by rw [add_comm]; exact hsum))

end OptimalOTS.LowerGenerality3
