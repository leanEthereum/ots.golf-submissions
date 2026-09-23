import Submissions.UpperLeanIsa.HiddenCharges

/-! Adaptive hidden-input bounds. The potential averages over records with the
same public information, so oracle queries may depend on all previous answers. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleSpec ENNReal
open scoped Classical
noncomputable section

attribute [local irreducible] hashBits publicFiber finiteFiber hiddenCache

local instance : DecidableEq Record := Classical.decEq Record

def hiddenPotential (d : Cut) (v : PublicData) (w : ℝ≥0∞) (c : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ publicFiber d v, if Cache.Hits c (hiddenCache d ξ) then w else 0

theorem hiddenPotential_cacheQuery (d : Cut) (v : PublicData) (w : ℝ≥0∞)
    (c : Cache) (q : Query) (u : BitVec hashBits) :
    hiddenPotential d v w (c.cacheQuery q u) ≤ hiddenPotential d v w c +
      (secondPreimageRate * ∑ _ξ ∈ publicFiber d v, w) * queryCost (.inr q) := by
  calc
    _ ≤ hiddenPotential d v w c +
        ∑ ξ ∈ publicFiber d v, if (hiddenCache d ξ q).isSome then w else 0 := by
      unfold hiddenPotential
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro ξ _
      rw [Cache.hits_cacheQuery]
      by_cases hp : Cache.Hits c (hiddenCache d ξ) <;>
        by_cases hq : (hiddenCache d ξ q).isSome <;>
        simp only [hp, hq, or_self, true_or, or_true, if_true, if_false, zero_add] <;>
        first | exact le_rfl | exact le_self_add
    _ ≤ hiddenPotential d v w c +
        secondPreimageRate * queryCost (.inr q) * ∑ _ξ ∈ publicFiber d v, w :=
      add_le_add le_rfl (hidden_input_charge d v q w)
    _ = _ := by rw [mul_right_comm secondPreimageRate]

theorem hiddenPotential_charge (d : Cut) (v : PublicData) (w : ℝ≥0∞)
    (c : Cache) (q : Query) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      hiddenPotential d v w (c.cacheQuery q u)) ≤ hiddenPotential d v w c +
      (secondPreimageRate * ∑ _ξ ∈ publicFiber d v, w) * queryCost (.inr q) := by
  calc
    _ ≤ ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (hiddenPotential d v w c +
          (secondPreimageRate * ∑ _ξ ∈ publicFiber d v, w) * queryCost (.inr q)) :=
      Finset.sum_le_sum fun u _ => mul_le_mul' le_rfl (hiddenPotential_cacheQuery d v w c q u)
    _ = _ := sum_inv_card_mul _

theorem hiddenPotential_zero (d : Cut) (v : PublicData) (w : ℝ≥0∞) (c : Cache)
    (hc : ∀ ξ ∈ publicFiber d v, Cache.Disjoint c (hiddenCache d ξ)) :
    hiddenPotential d v w c = 0 := by
  exact Finset.sum_eq_zero fun ξ hξ => if_neg ((hc ξ hξ).not_hits)

/-- A cost bound for the entire adaptive computation bounds its chance of
visiting a hidden programmed input, averaged over a public-data fiber. -/
theorem hidden_hit_bound {α : Type} (d : Cut) (v : PublicData) (w : ℝ≥0∞)
    (oa : OracleComp Spec α) (c : Cache) (B : ℕ) (hB : CostAtMost oa B)
    (hc : ∀ ξ ∈ publicFiber d v, Cache.Disjoint c (hiddenCache d ξ)) :
    E (run oa c) (fun p => hiddenPotential d v w p.2) ≤
      (secondPreimageRate * ∑ _ξ ∈ publicFiber d v, w) * B := by
  have h := master_single (secondPreimageRate * ∑ _ξ ∈ publicFiber d v, w)
    (hiddenPotential d v w) (fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun c _ q _ _ _ => hiddenPotential_charge d v w c q)
    oa (fun _ c => hiddenPotential d v w c) (fun _ _ => le_rfl) c B trivial hB
  rw [hiddenPotential_zero d v w c hc, zero_add] at h
  exact h

theorem hidden_hit_bound_from_exposure {α : Type} (d : Cut) (ζ : Record) (w : ℝ≥0∞)
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B) :
    E (run oa (exposedCache d ζ)) (fun p => hiddenPotential d (publicData d ζ) w p.2) ≤
      (secondPreimageRate * ∑ _ξ ∈ publicFiber d (publicData d ζ), w) * B := by
  apply hidden_hit_bound d (publicData d ζ) w oa (exposedCache d ζ) B hB
  intro ξ hξ
  have hdata := (mem_publicFiber d (publicData d ζ) ξ).mp hξ
  rw [← exposedCache_data_eq d ξ ζ hdata]
  exact exposure_disjoint d ξ

end
end OptimalOTS.LeanIsaBaseline
