import Submissions.UpperLeanIsa.RecordSemantics

/-! Replace hidden programmed answers by fresh random-oracle answers, charging
only the probability of touching a hidden input. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleComp.EvalDist OracleSpec ENNReal
open scoped Classical
noncomputable section

attribute [local irreducible] hashBits publicFiber finiteFiber hiddenCache

local instance : DecidableEq Record := Classical.decEq Record

theorem E_finset_sum {α J : Type} (p : ProbComp α) (S : Finset J)
    (f : J → α → ℝ≥0∞) :
    E p (fun x => ∑ j ∈ S, f j x) = ∑ j ∈ S, E p (f j) := by
  let : DecidableEq J := Classical.decEq J
  induction S using Finset.induction_on with
  | empty => simp [E, expectedValue_def]
  | @insert j S hj ih =>
    simp only [Finset.sum_insert hj, E, expectedValue_add]
    exact congrArg (fun t => E p (f j) + t) ih

theorem E_const_mul {α : Type} (p : ProbComp α) (w : ℝ≥0∞) (f : α → ℝ≥0∞) :
    E p (fun x => w * f x) = w * E p f := by
  simp only [mul_comm w, E, expectedValue_mul_const]

theorem E_weighted_sum {α J : Type} (p : ProbComp α) (S : Finset J)
    (w : ℝ≥0∞) (f : J → α → ℝ≥0∞) :
    E p (fun x => ∑ j ∈ S, w * f j x) = ∑ j ∈ S, w * E p (f j) := by
  rw [E_finset_sum]
  exact Finset.sum_congr rfl fun j _ => E_const_mul p w (f j)

/-- A public-data fiber may be averaged before the adaptive ideal computation.
Any additional cache entries are allowed if they avoid every hidden point. -/
theorem hidden_coupling {α : Type} (d : Cut) (v : PublicData) (w : ℝ≥0∞)
    (oa : OracleComp Spec α) (c : Cache) (B : ℕ) (hB : CostAtMost oa B)
    (hc : ∀ ξ ∈ publicFiber d v, Cache.Disjoint c (hiddenCache d ξ))
    (φ : Record → α × Cache → ℝ≥0∞) (hφ : ∀ ξ p, φ ξ p ≤ 1) :
    (∑ ξ ∈ publicFiber d v, w * E (run oa (Cache.extend c (hiddenCache d ξ))) (φ ξ)) ≤
      (secondPreimageRate * ∑ _ξ ∈ publicFiber d v, w) * B +
      E (run oa c) (fun p => ∑ ξ ∈ publicFiber d v,
        w * φ ξ (p.1, Cache.extend p.2 (hiddenCache d ξ))) := by
  calc
    _ ≤ ∑ ξ ∈ publicFiber d v, w * E (run oa c)
        (fun p => if Cache.Hits p.2 (hiddenCache d ξ) then 1
          else φ ξ (p.1, Cache.extend p.2 (hiddenCache d ξ))) := by
      apply Finset.sum_le_sum
      intro ξ hξ
      exact mul_le_mul' le_rfl (iub oa (hiddenCache d ξ) (φ ξ) (hφ ξ) c (hc ξ hξ))
    _ = E (run oa c) (fun p => ∑ ξ ∈ publicFiber d v,
        w * (if Cache.Hits p.2 (hiddenCache d ξ) then 1
          else φ ξ (p.1, Cache.extend p.2 (hiddenCache d ξ)))) :=
      (E_weighted_sum _ _ _ _).symm
    _ ≤ E (run oa c) (fun p => hiddenPotential d v w p.2 +
        ∑ ξ ∈ publicFiber d v, w * φ ξ (p.1, Cache.extend p.2 (hiddenCache d ξ))) := by
      apply E_mono
      intro p
      unfold hiddenPotential
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro ξ _
      by_cases hh : Cache.Hits p.2 (hiddenCache d ξ)
      · simp only [if_pos hh, mul_one]
        exact le_self_add
      · simp only [if_neg hh, zero_add]
        exact le_rfl
    _ = E (run oa c) (fun p => hiddenPotential d v w p.2) +
        E (run oa c) (fun p => ∑ ξ ∈ publicFiber d v,
          w * φ ξ (p.1, Cache.extend p.2 (hiddenCache d ξ))) := expectedValue_add _ _ _
    _ ≤ _ := add_le_add (hidden_hit_bound d v w oa c B hB hc) le_rfl

theorem record_coupling {α : Type} (d : Cut) (ζ : Record) (w : ℝ≥0∞)
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (φ : Record → α × Cache → ℝ≥0∞) (hφ : ∀ ξ p, φ ξ p ≤ 1) :
    (∑ ξ ∈ publicFiber d (publicData d ζ), w * E (run oa ξ.cache) (φ ξ)) ≤
      (secondPreimageRate * ∑ _ξ ∈ publicFiber d (publicData d ζ), w) * B +
      E (run oa (exposedCache d ζ)) (fun p => ∑ ξ ∈ publicFiber d (publicData d ζ),
        w * φ ξ (p.1, Cache.extend p.2 (hiddenCache d ξ))) := by
  have hc (ξ : Record) (hξ : ξ ∈ publicFiber d (publicData d ζ)) :
      exposedCache d ζ = exposedCache d ξ :=
    (exposedCache_data_eq d ξ ζ ((mem_publicFiber _ _ _).mp hξ)).symm
  have h := hidden_coupling d (publicData d ζ) w oa (exposedCache d ζ) B hB
    (fun ξ hξ => by rw [hc ξ hξ]; exact exposure_disjoint d ξ) φ hφ
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun ξ hξ => ?_)) h
  rw [hc ξ hξ, exposure_partition]

end
end OptimalOTS.LeanIsaBaseline
