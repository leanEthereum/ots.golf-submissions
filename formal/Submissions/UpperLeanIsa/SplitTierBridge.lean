import Submissions.UpperLeanIsa.SplitCount

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace OptimalOTS.LeanIsaBaseline.Layer.FourChildCodec
open scoped Classical

theorem accepted_weight_mem_of_count (keys WL : List ℕ)
    (hlen : WL.length ≤ keys.length)
    (hcount : ∀ w, (Finset.univ.filter fun I : Index =>
      params.Accepted I ∧ wprod I = w).card = WL.getD (keys.idxOf w) 0)
    {I : Index} (hI : params.Accepted I) : wprod I ∈ keys := by
  have hpos : 0 < (Finset.univ.filter fun J : Index =>
      params.Accepted J ∧ wprod J = wprod I).card :=
    Finset.card_pos.mpr ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hI,rfl⟩⟩
  rw [hcount] at hpos
  by_contra h
  rw [List.idxOf_of_notMem h, List.getD_eq_default _ _ hlen] at hpos
  omega

/-- An exact raw-index count is the required class-count certificate. The
already proved alias bijection supplies the true class weight. -/
theorem tierHyp_of_count (S : Tier.Sched) (keys WL : List ℕ)
    (hK : S.K = 127) (hsize : keys.length = S.T)
    (hweights : ∀ t < S.T, keys.getD t 0 = S.a t)
    (hdistinct : keys.Nodup) (hlen : WL.length ≤ keys.length)
    (hcounts : ∀ t < S.T, WL.getD t 0 = S.N t * S.a t)
    (hcount : ∀ w, (Finset.univ.filter fun I : Index =>
      params.Accepted I ∧ wprod I = w).card = WL.getD (keys.idxOf w) 0) :
    params.TierHyp S where
  K_eq := hK
  weight_mem := by
    intro I hI
    have hm := accepted_weight_mem_of_count keys WL hlen hcount hI
    obtain ⟨t,ht,he⟩ := List.mem_iff_getElem.mp hm
    have hT : t < S.T := by rw [hsize] at ht; exact ht
    refine ⟨t,hT,?_⟩
    rw [weight_eq hI]
    rw [← hweights t hT, List.getD_eq_getElem _ _ ht]
    exact he.symm
  card_weight := by
    intro t ht
    have hget : keys[t]'(by rw [hsize]; exact ht) = S.a t := by
      rw [← hweights t ht, List.getD_eq_getElem _ _ (by rw [hsize]; exact ht)]
    have hidx : keys.idxOf (S.a t) = t := by
      rw [← hget]
      exact hdistinct.idxOf_getElem t (by rw [hsize]; exact ht)
    have hfilter : (Finset.univ.filter fun I : Index =>
        params.Accepted I ∧ params.weight I = S.a t) =
        (Finset.univ.filter fun I : Index =>
        params.Accepted I ∧ wprod I = S.a t) := by
      apply Finset.filter_congr
      intro I _
      constructor <;> intro h
      · exact ⟨h.1, (weight_eq h.1).symm.trans h.2⟩
      · exact ⟨h.1, (weight_eq h.1).trans h.2⟩
    rw [hfilter, hcount, hidx]
    exact hcounts t ht

end OptimalOTS.LeanIsaBaseline.Layer.FourChildCodec
