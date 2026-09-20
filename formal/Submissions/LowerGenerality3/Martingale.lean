import Submissions.LowerGenerality3.Useful
import Submissions.LowerGenerality3.Expectation

/-!
# The cache martingale

For a finite set `Q` of queries, a predicate `P` on answers and a base cache `c₀`, the event
`Dec c₀ P Q c` says the cache `c` holds, at some `q ∈ Q` fresh relative to `c₀`, an answer
satisfying `P`. The functional `Sm c₀ P Q c` (zero once decided, otherwise the product of the
non-`P` rates over the fresh, still unanswered members of `Q`) has the same expectation before
and after any computation (`E_Sm_run`). Hence any run from `c₀` decides `Q` with probability at
most `1 − Sm c₀ P Q c₀` (`E_dec_le`), and a run that answers all of `Q` decides it with exactly
that probability (`E_dec_queryAll`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

variable (c₀ : Cache) (P : Query → BitVec hashBits → Prop) (Q : Finset Query)

/-- The rate of `P` at `q` over a uniform answer. -/
def pr (q : Query) : ℝ≥0∞ :=
  Pr[= true | (fun y => decide (P q y)) <$> ($ᵗ BitVec hashBits : ProbComp _)]

/-- The cache holds a `P`-answer at a member of `Q` that `c₀` did not hold. -/
def Dec (c : Cache) : Prop := ∃ q ∈ Q, c₀ q = none ∧ ∃ y, c q = some y ∧ P q y

/-- The members of `Q` fresh for `c₀` and still unanswered in `c`. -/
def open_ (c : Cache) : Finset Query := Q.filter fun q => c₀ q = none ∧ c q = none

/-- The martingale. -/
def Sm (c : Cache) : ℝ≥0∞ := if Dec c₀ P Q c then 0 else ∏ q ∈ open_ c₀ Q c, (1 - pr P q)

theorem pr_le_one (q : Query) : pr P q ≤ 1 := probOutput_le_one

/-- The probability of a non-`P` answer. -/
theorem E_not_P (q : Query) :
    E ($ᵗ BitVec hashBits) (fun y => if P q y then 0 else 1) = 1 - pr P q := by
  have hs0 := probOutput_true_add_false ((fun y => decide (P q y)) <$> ($ᵗ BitVec hashBits : ProbComp _))
  have hs : Pr[= true | (fun y => decide (P q y)) <$> ($ᵗ BitVec hashBits : ProbComp _)] +
      Pr[= false | (fun y => decide (P q y)) <$> ($ᵗ BitVec hashBits : ProbComp _)] = 1 := by
    simpa using hs0
  have hf : Pr[= false | (fun y => decide (P q y)) <$> ($ᵗ BitVec hashBits : ProbComp _)] =
      E ($ᵗ BitVec hashBits) (fun y => if P q y then 0 else 1) := by
    rw [map_eq_bind_pure_comp, probOutput_bind_eq_expectedValue]
    refine congrArg _ (funext fun y => ?_)
    simp only [Function.comp_apply, probOutput_pure]
    by_cases h : P q y <;> simp [h]
  rw [← hf]
  exact ENNReal.eq_sub_of_add_eq ((pr_le_one P q).trans_lt ENNReal.one_lt_top).ne
    (by rw [add_comm]; exact hs)

/-- `Dec` only grows with the cache. -/
theorem Dec.mono {c c' : Cache} (h : Cache.Sub c c') (hd : Dec c₀ P Q c) : Dec c₀ P Q c' := by
  obtain ⟨q, hq, h0, y, hy, hp⟩ := hd
  exact ⟨q, hq, h0, y, h q y hy, hp⟩

/-- One fresh answer at `q₀` keeps the expectation of `Sm`. -/
theorem E_Sm_step (c : Cache) (q₀ : Query) (hc : c q₀ = none) :
    E ($ᵗ BitVec hashBits) (fun u => Sm c₀ P Q (c.cacheQuery q₀ u)) = Sm c₀ P Q c := by
  by_cases hdec : Dec c₀ P Q c
  · have hz : (fun u => Sm c₀ P Q (c.cacheQuery q₀ u)) = fun _ => (0 : ℝ≥0∞) := funext fun u => by
      simp only [Sm, if_pos (Dec.mono c₀ P Q (Cache.sub_cacheQuery_of_none hc u) hdec)]
    rw [hz, E_const]
    simp only [Sm, if_pos hdec]
  · by_cases hq : q₀ ∈ Q ∧ c₀ q₀ = none
    · -- the query is a fresh member of `Q`: it is decided now
      have hopen : q₀ ∈ open_ c₀ Q c := Finset.mem_filter.mpr ⟨hq.1, hq.2, hc⟩
      have hdec' : ∀ u, Dec c₀ P Q (c.cacheQuery q₀ u) ↔ P q₀ u := by
        intro u
        constructor
        · rintro ⟨q, hqQ, h0, y, hy, hp⟩
          by_cases he : q = q₀
          · subst he
            rw [QueryCache.cacheQuery_self] at hy
            cases hy; exact hp
          · rw [QueryCache.cacheQuery_of_ne _ _ he] at hy
            exact (hdec ⟨q, hqQ, h0, y, hy, hp⟩).elim
        · intro hp
          exact ⟨q₀, hq.1, hq.2, u, QueryCache.cacheQuery_self _ _ _, hp⟩
      have hopen' : ∀ u, open_ c₀ Q (c.cacheQuery q₀ u) = (open_ c₀ Q c).erase q₀ := by
        intro u
        ext q
        simp only [open_, Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hqQ, h0, hn⟩
          have hne : q ≠ q₀ := fun e => by
            subst e; rw [QueryCache.cacheQuery_self] at hn; cases hn
          rw [QueryCache.cacheQuery_of_ne _ _ hne] at hn
          exact ⟨hne, hqQ, h0, hn⟩
        · rintro ⟨hne, hqQ, h0, hn⟩
          rw [QueryCache.cacheQuery_of_ne _ _ hne]
          exact ⟨hqQ, h0, hn⟩
      have hfun : (fun u => Sm c₀ P Q (c.cacheQuery q₀ u)) =
          fun u => (if P q₀ u then 0 else 1) * ∏ q ∈ (open_ c₀ Q c).erase q₀, (1 - pr P q) := by
        funext u
        simp only [Sm, hdec' u, hopen' u]
        by_cases hp : P q₀ u <;> simp [hp]
      have hmul : E ($ᵗ BitVec hashBits) (fun u => (if P q₀ u then 0 else 1) *
          ∏ q ∈ (open_ c₀ Q c).erase q₀, (1 - pr P q)) =
          E ($ᵗ BitVec hashBits) (fun u => if P q₀ u then 0 else 1) *
            ∏ q ∈ (open_ c₀ Q c).erase q₀, (1 - pr P q) := by
        rw [E_uniform, E_uniform, Finset.sum_mul]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [hfun, hmul, E_not_P,
        show Sm c₀ P Q c = ∏ q ∈ open_ c₀ Q c, (1 - pr P q) by simp only [Sm, if_neg hdec],
        ← Finset.mul_prod_erase _ _ hopen]
    · -- outside `Q` or not fresh: nothing changes
      have hdec' : ∀ u, ¬ Dec c₀ P Q (c.cacheQuery q₀ u) := by
        rintro u ⟨q, hqQ, h0, y, hy, hp⟩
        by_cases he : q = q₀
        · subst he; exact hq ⟨hqQ, h0⟩
        · rw [QueryCache.cacheQuery_of_ne _ _ he] at hy
          exact hdec ⟨q, hqQ, h0, y, hy, hp⟩
      have hopen' : ∀ u, open_ c₀ Q (c.cacheQuery q₀ u) = open_ c₀ Q c := by
        intro u
        ext q
        simp only [open_, Finset.mem_filter]
        by_cases he : q = q₀
        · subst he
          simp only [QueryCache.cacheQuery_self]
          constructor
          · rintro ⟨_, _, h⟩; cases h
          · rintro ⟨hqQ, h0, -⟩; exact (hq ⟨hqQ, h0⟩).elim
        · rw [QueryCache.cacheQuery_of_ne _ _ he]
      have hfun : (fun u => Sm c₀ P Q (c.cacheQuery q₀ u)) = fun _ => Sm c₀ P Q c := by
        funext u
        simp only [Sm, if_neg (hdec' u), if_neg hdec, hopen' u]
      rw [hfun]
      exact E_const _ _

/-- The expectation of `Sm` is unchanged by any computation. -/
theorem E_Sm_run {α : Type} (oa : OracleComp Spec α) :
    ∀ c : Cache, E (run oa c) (fun p => Sm c₀ P Q p.2) = Sm c₀ P Q c := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro c; rw [run_pure, E_pure]
  | query_bind t k ih =>
    intro c
    rw [run_query_bind, E_bind]
    rcases t with t | q
    · rw [oracleImpl_run_inl]
      simp only [bind_assoc, pure_bind, E_bind, E_pure]
      simp only [ih]
      exact E_const _ _
    · rcases hc : c q with _ | v
      · rw [oracleImpl_run_inr_none hc]
        simp only [bind_assoc, pure_bind, E_bind, E_pure]
        simp only [ih]
        exact E_Sm_step c₀ P Q c q hc
      · rw [oracleImpl_run_inr_some hc, E_pure]
        exact ih v c

theorem Sm_add_ind_le_one (c : Cache) : Sm c₀ P Q c + (if Dec c₀ P Q c then 1 else 0) ≤ 1 := by
  by_cases h : Dec c₀ P Q c
  · simp [Sm, h]
  · simp only [Sm, if_neg h, add_zero]
    exact Finset.prod_le_one (fun _ _ => zero_le) (fun q _ => tsub_le_self)

/-- A run from `c₀` decides `Q` with probability at most `1 − Sm c₀`. -/
theorem E_dec_le {α : Type} (oa : OracleComp Spec α) :
    E (run oa c₀) (fun p => if Dec c₀ P Q p.2 then 1 else 0) ≤ 1 - Sm c₀ P Q c₀ := by
  have h := E_Sm_run c₀ P Q oa c₀
  have hsum : E (run oa c₀) (fun p => Sm c₀ P Q p.2) +
      E (run oa c₀) (fun p => if Dec c₀ P Q p.2 then 1 else 0) ≤ 1 := by
    rw [← expectedValue_add]
    calc _ ≤ E (run oa c₀) (fun _ => (1 : ℝ≥0∞)) :=
          E_mono _ fun p => Sm_add_ind_le_one c₀ P Q p.2
      _ = 1 := E_const _ _
  rw [h] at hsum
  exact ENNReal.le_sub_of_add_le_left (by
    rw [Sm]; split_ifs
    · exact ENNReal.zero_ne_top
    · exact (ENNReal.prod_lt_top (fun q _ => tsub_le_self.trans_lt ENNReal.one_lt_top)).ne) hsum


/-! ## Answering a whole list of queries -/

/-- Query every member of a list, in order. -/
def queryAll : List Query → OracleComp Spec Unit
  | [] => pure ()
  | q :: l => (liftM (Spec.query (.inr q)) : OracleComp Spec (BitVec hashBits)) >>= fun _ => queryAll l

/-- After `queryAll l`, every member of `l` is cached. -/
theorem cached_of_queryAll (l : List Query) :
    ∀ (c : Cache) (p : Unit × Cache), p ∈ support (run (queryAll l) c) →
      ∀ q ∈ l, (p.2 q).isSome := by
  induction l with
  | nil =>
    intro c p hp q hq
    exact absurd hq (List.not_mem_nil)
  | cons q₀ l ih =>
    intro c p hp q hq
    simp only [queryAll] at hp
    rw [run_bind, run_query, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
    have hsub : Cache.Sub c' p.2 := sub_of_mem_support_run _ _ _ hp
    have hc' : (c' q₀).isSome := by
      rcases hc : c q₀ with _ | v
      · rw [oracleImpl_run_inr_none hc, support_bind] at hu
        simp only [Set.mem_iUnion] at hu
        obtain ⟨w, -, hw⟩ := hu
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        simp [QueryCache.cacheQuery_self]
      · rw [oracleImpl_run_inr_some hc, support_pure] at hu
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        simp [hc]
    rcases List.mem_cons.mp hq with rfl | hql
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hc'
      rw [hsub q v hv]; rfl
    · exact ih c' p hp q hql

theorem cost_queryAll (l : List Query) (hl : ∀ q ∈ l, q.1 ≤ 512) :
    CostAtMost (queryAll l) l.length := by
  induction l with
  | nil => trivial
  | cons q₀ l ih =>
    have hq := hl q₀ List.mem_cons_self
    have hrest := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    simp only [queryAll, List.length_cons]
    unfold CostAtMost
    rw [isQueryBound_query_bind_iff]
    have hb : blockCost q₀.1 = 1 := by unfold blockCost blockBits; omega
    refine ⟨?_, fun _ => ?_⟩
    · change blockCost q₀.1 ≤ l.length + 1
      omega
    · change (queryAll l).IsQueryBound (l.length + 1 - blockCost q₀.1) _ _
      rw [hb, Nat.add_sub_cancel]
      exact hrest

/-- Once every member of `Q` is cached, `Sm` is the indicator of not being decided. -/
theorem Sm_eq_of_cached {c : Cache} (hc : ∀ q ∈ Q, (c q).isSome) :
    Sm c₀ P Q c = if Dec c₀ P Q c then 0 else 1 := by
  unfold Sm
  split_ifs with h
  · rfl
  · have hempty : open_ c₀ Q c = ∅ := by
      ext q
      simp only [open_, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hq _ hn
      have := hc q hq
      rw [hn] at this
      simp at this
    rw [hempty, Finset.prod_empty]

/-- Answering a list containing `Q` decides it with probability exactly `1 − Sm c₀`. -/
theorem E_dec_queryAll (l : List Query) (hQ : ∀ q ∈ Q, q ∈ l) :
    E (run (queryAll l) c₀) (fun p => if Dec c₀ P Q p.2 then 1 else 0) = 1 - Sm c₀ P Q c₀ := by
  have h := E_Sm_run c₀ P Q (queryAll l) c₀
  have hS : E (run (queryAll l) c₀) (fun p => Sm c₀ P Q p.2) =
      E (run (queryAll l) c₀) (fun p => if Dec c₀ P Q p.2 then 0 else 1) := by
    apply le_antisymm
    · apply expectedValue_mono_of_support
      intro p hp
      rw [Sm_eq_of_cached c₀ P Q (fun q hq => cached_of_queryAll l c₀ p hp q (hQ q hq))]
    · apply expectedValue_mono_of_support
      intro p hp
      rw [Sm_eq_of_cached c₀ P Q (fun q hq => cached_of_queryAll l c₀ p hp q (hQ q hq))]
  have hsum : E (run (queryAll l) c₀) (fun p => if Dec c₀ P Q p.2 then 0 else 1) +
      E (run (queryAll l) c₀) (fun p => if Dec c₀ P Q p.2 then 1 else 0) = 1 := by
    rw [← expectedValue_add]
    calc _ = E (run (queryAll l) c₀) (fun _ => (1 : ℝ≥0∞)) := by
          apply congrArg; funext p; split_ifs <;> simp
      _ = 1 := E_const _ _
  rw [← hS, h] at hsum
  exact (ENNReal.eq_sub_of_add_eq (by
    rw [Sm]; split_ifs
    · exact ENNReal.zero_ne_top
    · exact (ENNReal.prod_lt_top (fun q _ => tsub_le_self.trans_lt ENNReal.one_lt_top)).ne)
    (by rw [add_comm]; exact hsum))

end OptimalOTS.LowerGenerality3
