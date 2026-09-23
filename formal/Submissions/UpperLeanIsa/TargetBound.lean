import Submissions.UpperLeanIsa.Master

/-! A cost-aware bound on adaptive queries hitting specified output targets.
Targets may depend on the query. This is a probability lemma, not the complete OTS reduction. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleSpec ENNReal
open scoped Classical
noncomputable section

attribute [local irreducible] hashBits

def TargetHit (targets : Query → Finset (BitVec hashBits)) (c : Cache) : Prop :=
  ∃ q u, c q = some u ∧ u ∈ targets q

def targetPotential (targets : Query → Finset (BitVec hashBits)) (c : Cache) : ℝ≥0∞ :=
  if TargetHit targets c then 1 else 0

theorem targetHit_cacheQuery (targets : Query → Finset (BitVec hashBits))
    (c : Cache) (q : Query) (u : BitVec hashBits) (hc : c q = none) :
    TargetHit targets (c.cacheQuery q u) ↔ TargetHit targets c ∨ u ∈ targets q := by
  constructor
  · rintro ⟨p, v, hv, ht⟩
    by_cases hp : p = q
    · subst p
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hv
      exact Or.inr (hv ▸ ht)
    · rw [QueryCache.cacheQuery_of_ne _ _ hp] at hv
      exact Or.inl ⟨p, v, hv, ht⟩
  · rintro (⟨p, v, hv, ht⟩ | ht)
    · have hp : p ≠ q := by rintro rfl; simp [hc] at hv
      exact ⟨p, v, by rwa [QueryCache.cacheQuery_of_ne _ _ hp], ht⟩
    · exact ⟨q, u, QueryCache.cacheQuery_self _ _ _, ht⟩

theorem target_charge (targets : Query → Finset (BitVec hashBits))
    (κ : ℝ≥0∞)
    (hcharge : ∀ q, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (targets q).card ≤
      κ * queryCost (.inr q))
    (c : Cache) (q : Query) (hc : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      targetPotential targets (c.cacheQuery q u)) ≤
        targetPotential targets c + κ * queryCost (.inr q) := by
  by_cases hh : TargetHit targets c
  · have hp (d : Cache) : targetPotential targets d ≤ 1 := by
      unfold targetPotential
      split <;> simp
    calc
      _ ≤ ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * 1 :=
        Finset.sum_le_sum fun u _ => mul_le_mul' le_rfl (hp _)
      _ = 1 := sum_inv_card_mul 1
      _ ≤ _ := by simp only [targetPotential, if_pos hh]; exact le_self_add
  · simp only [targetPotential, targetHit_cacheQuery targets c q _ hc, hh, false_or, if_false]
    rw [← Finset.mul_sum]
    have hs : (∑ u : BitVec hashBits, if u ∈ targets q then (1 : ℝ≥0∞) else 0) =
        ((targets q).card : ℝ≥0∞) := by simp
    rw [hs, zero_add]
    exact hcharge q

/-- An arbitrary adaptive computation, including free private randomness, cannot
increase the probability of a target hit faster than the allowed per-compression charge. -/
theorem target_hit_bound {α : Type} (targets : Query → Finset (BitVec hashBits))
    (κ : ℝ≥0∞)
    (hcharge : ∀ q, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (targets q).card ≤
      κ * queryCost (.inr q))
    (oa : OracleComp Spec α) (c : Cache) (B : ℕ)
    (hB : CostAtMost oa B) (hc : ¬ TargetHit targets c) :
    E (run oa c) (fun p => targetPotential targets p.2) ≤ κ * B := by
  have h := master_single κ (targetPotential targets) (fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun c _ q _ hq _ => target_charge targets κ hcharge c q hq)
    oa (fun _ d => targetPotential targets d) (fun _ _ => le_rfl) c B trivial hB
  simpa only [targetPotential, if_neg hc, zero_add] using h

end
end OptimalOTS.LeanIsaBaseline
