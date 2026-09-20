import Submissions.LowerGenerality3.Martingale

/-!
# The fresh-query union bound

If every query has a `P`-rate at most `τ'`, a computation of cost `b` produces, at a point fresh
for the base cache, a `P`-answer with probability at most `τ' · b` (`E_bad_le`). This is the
adaptive union bound over the signer's fresh queries.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget

variable (c₀ : Cache) (P : Query → BitVec hashBits → Prop)

/-- The cache holds a `P`-answer at a point fresh for `c₀`. -/
def Bad (c : Cache) : Prop := ∃ q y, c₀ q = none ∧ c q = some y ∧ P q y

theorem Bad.mono {c c' : Cache} (h : Cache.Sub c c') (hb : Bad c₀ P c) : Bad c₀ P c' := by
  obtain ⟨q, y, h0, hy, hp⟩ := hb
  exact ⟨q, y, h0, h q y hy, hp⟩

/-- The indicator of `Bad`. -/
def badInd (c : Cache) : ℝ≥0∞ := if Bad c₀ P c then 1 else 0

/-- The probability of a `P`-answer at a fresh query. -/
theorem E_P (q : Query) : E ($ᵗ BitVec hashBits) (fun y => if P q y then 1 else 0) = pr P q := by
  rw [pr, map_eq_bind_pure_comp, probOutput_bind_eq_expectedValue]
  refine congrArg _ (funext fun y => ?_)
  simp only [Function.comp_apply, probOutput_pure]
  by_cases h : P q y <;> simp [h]

/-- One fresh answer raises the expected indicator by at most the rate at that point. -/
theorem E_bad_step (c : Cache) (q₀ : Query) (hc : c q₀ = none) :
    E ($ᵗ BitVec hashBits) (fun u => badInd c₀ P (c.cacheQuery q₀ u)) ≤ badInd c₀ P c + pr P q₀ := by
  by_cases hb : Bad c₀ P c
  · have hz : (fun u => badInd c₀ P (c.cacheQuery q₀ u)) = fun _ => (1 : ℝ≥0∞) := funext fun u => by
      simp only [badInd, if_pos (Bad.mono c₀ P (Cache.sub_cacheQuery_of_none hc u) hb)]
    rw [hz, E_const]
    simp only [badInd, if_pos hb]
    exact le_self_add
  · have hstep : ∀ u, badInd c₀ P (c.cacheQuery q₀ u) ≤ if P q₀ u then 1 else 0 := by
      intro u
      unfold badInd
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso
        obtain ⟨q, y, h0, hy, hp⟩ := h1
        by_cases he : q = q₀
        · subst he
          rw [QueryCache.cacheQuery_self] at hy
          cases hy
          exact h2 hp
        · rw [QueryCache.cacheQuery_of_ne _ _ he] at hy
          exact hb ⟨q, y, h0, hy, hp⟩
      · exact zero_le
      · exact le_rfl
    calc E ($ᵗ BitVec hashBits) (fun u => badInd c₀ P (c.cacheQuery q₀ u))
        ≤ E ($ᵗ BitVec hashBits) (fun u => if P q₀ u then 1 else 0) := E_mono _ hstep
      _ = pr P q₀ := E_P P q₀
      _ ≤ badInd c₀ P c + pr P q₀ := le_add_self

/-- The adaptive union bound: cost `b` buys at most `τ' · b` of `Bad`. -/
theorem E_bad_le {τ' : ℝ≥0∞} (hP : ∀ q, pr P q ≤ τ') {α : Type} (oa : OracleComp Spec α) :
    ∀ (b : ℕ) (c : Cache), CostAtMost oa b →
      E (run oa c) (fun p => badInd c₀ P p.2) ≤ badInd c₀ P c + τ' * b := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro b c _
    rw [run_pure, E_pure]
    exact le_self_add
  | query_bind t k ih =>
    intro b c hcost
    unfold CostAtMost at hcost
    rw [isQueryBound_query_bind_iff] at hcost
    rw [run_query_bind, E_bind]
    rcases t with t | q
    · rw [oracleImpl_run_inl]
      simp only [bind_assoc, pure_bind, E_bind, E_pure]
      have hk : ∀ u, CostAtMost (k u) b := fun u => by
        have := hcost.2 u
        simpa [CostAtMost, queryCost] using this
      calc _ ≤ E (HasQuery.query (spec := unifSpec) (m := ProbComp) t)
            (fun _ => badInd c₀ P c + τ' * b) := E_mono _ fun u => ih u b c (hk u)
        _ = _ := E_const _ _
    · have hcost1 : 1 ≤ b := by
        have := hcost.1
        change blockCost q.1 ≤ b at this
        unfold blockCost at this
        omega
      have hk : ∀ u, CostAtMost (k u) (b - 1) := fun u => by
        have := hcost.2 u
        change CostAtMost (k u) (b - blockCost q.1) at this
        refine Costs.CostAtMost.mono this ?_
        unfold blockCost
        omega
      rcases hc : c q with _ | v
      · rw [oracleImpl_run_inr_none hc]
        simp only [bind_assoc, pure_bind, E_bind, E_pure]
        calc E ($ᵗ BitVec hashBits) (fun u => E (run (k u) (c.cacheQuery q u)) (fun p => badInd c₀ P p.2))
            ≤ E ($ᵗ BitVec hashBits) (fun u => badInd c₀ P (c.cacheQuery q u) + τ' * (b - 1 : ℕ)) :=
              E_mono _ fun u => ih u (b - 1) _ (hk u)
          _ = E ($ᵗ BitVec hashBits) (fun u => badInd c₀ P (c.cacheQuery q u)) + τ' * (b - 1 : ℕ) := by
              rw [E_uniform, E_uniform]
              simp only [mul_add, Finset.sum_add_distrib]
              congr 1
              have h := E_const ($ᵗ BitVec hashBits) (τ' * ((b - 1 : ℕ) : ℝ≥0∞))
              rwa [E_uniform] at h
          _ ≤ badInd c₀ P c + pr P q + τ' * (b - 1 : ℕ) :=
              add_le_add_left (E_bad_step c₀ P c q hc) _
          _ ≤ badInd c₀ P c + τ' * b := by
              rw [add_assoc]
              refine add_le_add_right ?_ _
              calc pr P q + τ' * (b - 1 : ℕ) ≤ τ' + τ' * (b - 1 : ℕ) := add_le_add_left (hP q) _
                _ = τ' * ((1 : ℕ) + (b - 1 : ℕ)) := by rw [mul_add, Nat.cast_one, mul_one]
                _ = τ' * b := by
                    congr 1
                    norm_cast
                    omega
      · rw [oracleImpl_run_inr_some hc, E_pure]
        calc _ ≤ badInd c₀ P c + τ' * (b - 1 : ℕ) := ih v (b - 1) c (hk v)
          _ ≤ badInd c₀ P c + τ' * b := by
              refine add_le_add_right (mul_le_mul' le_rfl ?_) _
              exact_mod_cast Nat.sub_le b 1

end OptimalOTS.LowerGenerality3
