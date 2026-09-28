import Submissions.UpperLeanIsa.FourConcrete
import Submissions.UpperLeanIsa.FourCoherence
import Submissions.UpperLeanIsa.FourBinding
import Submissions.UpperLeanIsa.FourSecurity

namespace OptimalOTS.LeanIsaBaseline.Layer.FourFusion
open scoped Classical
noncomputable section

def bindingUnit (u : Fin 8) : ℕ := ![5,6,0,8,9,10,11,12] u

theorem bindingUnit_lt (u : Fin 8) : bindingUnit u < 13 := by fin_cases u <;> decide

theorem bindingUnit_binding (u : Fin 8) :
    SplitTables.binding (bindingUnit u) = true := by fin_cases u <;> decide

theorem binding_visible_positive (I : Index) (hI : params.codec.Accepted I) (u : Fin 8) :
    0 < ((FourChildCodec.tup (bindingUnit u)
      (FourChildCodec.field (bindingUnit u) I)).take (SplitTables.visible (bindingUnit u))).sum := by
  have hu := bindingUnit_lt u
  have hs : FourChildCodec.ushape (bindingUnit u) = bindingUnit u := Nat.mod_eq_of_lt hu
  have hl := (FourChildCodec.not_dummy_iff I).mp ((FourChildCodec.accepted_iff I).mp hI).1
    (bindingUnit u) hu
  have hcut : FourChildCodec.field (bindingUnit u) I < FourChildCodec.cutS (bindingUnit u) := by
    simpa only [FourChildCodec.cut, hs] using hl
  simpa only [FourChildCodec.tup, hs] using
    FourChildCodec.visible_tuple_pos hu hcut (bindingUnit_binding u)

theorem parents_sum (I : Index) (u : Fin 8) :
    ∑ k ∈ parents u, FourChildCodec.digitN I k =
      ((FourChildCodec.tup (bindingUnit u) (FourChildCodec.field (bindingUnit u) I)).take
        (SplitTables.visible (bindingUnit u))).sum := by
  have hh : ∀ v < 13,
      ∑ i ∈ Finset.range (SplitTables.visible v),
        (FourChildCodec.tup v (FourChildCodec.field v I)).getD i 0 =
          ((FourChildCodec.tup v (FourChildCodec.field v I)).take
            (SplitTables.visible v)).sum := by
    intro v hv
    have hf := FourChildCodec.field_lt' hv I
    have hn : SplitTables.visible v ≤ (FourChildCodec.tup v (FourChildCodec.field v I)).length := by
      rw [FourChildCodec.tup_length hf]
      change SplitTables.dim v - SplitTables.hidden v ≤ SplitTables.dim (v % 13)
      rw [Nat.mod_eq_of_lt hv]
      omega
    rw [← FourChildCodec.sum_range_getD, List.length_take, min_eq_left hn]
    apply Finset.sum_congr rfl
    intro i hi
    exact (getD_take _ _ _ (Finset.mem_range.mp hi)).symm
  have h := hh (bindingUnit u) (bindingUnit_lt u)
  fin_cases u <;>
    simpa [parents, Fusion.SplitRoot.parents, Fusion.SplitRoot.parentList, bindingUnit,
      FourChildCodec.digitN, FourChildCodec.unitOf, FourChildCodec.coordOf,
      SplitTables.visible, SplitTables.dim, SplitTables.hidden,
      Finset.sum_range_succ, add_assoc] using h

/-- Every accepted signature has a nonzero visible parent in each of the eight groups. -/
theorem accepted_active (I : Index) (hI : params.codec.Accepted I) (u : Fin 8) :
    0 < ∑ k ∈ parents u, FourChildCodec.digitN I k := by
  rw [parents_sum]
  exact binding_visible_positive I hI u

theorem accepted_parent (I : Index) (hI : params.codec.Accepted I) (u : Fin 8) :
    ∃ k : Fin 42, k.val ∈ parents u ∧ 0 < params.codec.digit I k := by
  have hpos := accepted_active I hI u
  by_contra hn
  have hz : ∀ k ∈ parents u, FourChildCodec.digitN I k = 0 := by
    intro k hk
    have hlt := parents_bounded u k hk
    by_contra hne
    exact hn ⟨⟨k,hlt⟩,hk,by change 0 < FourChildCodec.digitN I k; omega⟩
  have hs : (∑ k ∈ parents u, FourChildCodec.digitN I k) = 0 :=
    Finset.sum_eq_zero hz
  omega


theorem params_securityHyp : params.SecurityHyp where
  toHyp := params_hyp
  ordered := concrete_ordered
  binding := accepted_parent

theorem concrete_secure : params.scheme.Secure := params.secure params_securityHyp

end
end OptimalOTS.LeanIsaBaseline.Layer.FourFusion
