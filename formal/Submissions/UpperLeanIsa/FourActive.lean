import Submissions.UpperLeanIsa.FourConcrete
import Submissions.UpperLeanIsa.FourCoherence
import Submissions.UpperLeanIsa.FourBinding

namespace OptimalOTS.LeanIsaBaseline.Layer.FourFusion
open scoped Classical
noncomputable section

def bindingUnit (u : Fin 9) : ℕ := ![5,6,0,7,8,9,10,11,12] u

theorem bindingUnit_lt (u : Fin 9) : bindingUnit u < 13 := by fin_cases u <;> decide

theorem bindingUnit_zero_empty : ∀ u : Fin 9,
    FourChildCodec.AS (FourChildCodec.ushape (bindingUnit u)) 1 = 0 := by decide +kernel

theorem binding_cost_positive (I : Index) (hI : params.codec.Accepted I) (u : Fin 9) :
    0 < FourChildCodec.cost (bindingUnit u) (FourChildCodec.field (bindingUnit u) I) := by
  have hl := (FourChildCodec.not_dummy_iff I).mp ((FourChildCodec.accepted_iff I).mp hI).1
    (bindingUnit u) (bindingUnit_lt u)
  have hb := FourChildCodec.cost_spec hl
  by_contra hn
  have hz : FourChildCodec.cost (bindingUnit u) (FourChildCodec.field (bindingUnit u) I) = 0 := by omega
  rw [hz, show 0+1=1 from rfl, bindingUnit_zero_empty u] at hb
  omega

theorem parents_sum (I : Index) (u : Fin 9) :
    ∑ k ∈ parents u, FourChildCodec.digitN I k =
      FourChildCodec.cost (bindingUnit u) (FourChildCodec.field (bindingUnit u) I) := by
  have hh : ∀ v < 13,
      ∑ i ∈ Finset.range (FourChildCodec.shK (FourChildCodec.ushape v)),
        (FourChildCodec.tup v (FourChildCodec.field v I)).getD i 0 =
          FourChildCodec.cost v (FourChildCodec.field v I) := by
    intro v hv
    have hf := FourChildCodec.field_lt' hv I
    rw [← FourChildCodec.tup_sum hf, ← FourChildCodec.sum_range_getD, FourChildCodec.tup_length hf]
  have h := hh (bindingUnit u) (bindingUnit_lt u)
  fin_cases u <;>
    simpa [parents, Fusion.FourChildRoot.parents, Fusion.FourChildRoot.parentList, bindingUnit, FourChildCodec.digitN, FourChildCodec.unitOf, FourChildCodec.coordOf,
      FourChildCodec.shK, FourChildCodec.ushape, Finset.sum_range_succ, add_assoc] using h

/-- Every accepted signature executes a final binding step in each of the nine groups. -/
theorem accepted_active (I : Index) (hI : params.codec.Accepted I) (u : Fin 9) :
    0 < ∑ k ∈ parents u, FourChildCodec.digitN I k := by
  rw [parents_sum]
  exact binding_cost_positive I hI u

theorem accepted_parent (I : Index) (hI : params.codec.Accepted I) (u : Fin 9) :
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

/-- Structural hypotheses required by the fused reconstruction security proof. -/
structure Params.SecurityHyp (P : Params) extends P.Hyp where
  ordered : P.locationOrder.Pairwise Earlier
  binding : ∀ I, P.codec.Accepted I → ∀ u : Fin 9,
    ∃ k : Fin 42, k.val ∈ parents u ∧ 0 < P.codec.digit I k

instance {P : Params} : Coe P.SecurityHyp P.Hyp := ⟨fun h => h.toHyp⟩

theorem params_securityHyp : params.SecurityHyp where
  toHyp := params_hyp
  ordered := concrete_ordered
  binding := accepted_parent

end
end OptimalOTS.LeanIsaBaseline.Layer.FourFusion
