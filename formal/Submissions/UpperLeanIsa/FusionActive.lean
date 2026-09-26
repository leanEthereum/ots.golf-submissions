import Submissions.UpperLeanIsa.FusionConcrete
import Submissions.UpperLeanIsa.FusionCoherence
import Submissions.UpperLeanIsa.FusionBinding

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open scoped Classical
noncomputable section

def bindingUnit (u : Fin 6) : ℕ := ![0,5,6,7,8,9] u

theorem bindingUnit_lt (u : Fin 6) : bindingUnit u < 13 := by fin_cases u <;> decide

theorem bindingUnit_zero_empty : ∀ u : Fin 6,
    FusionCodec.AS (FusionCodec.ushape (bindingUnit u)) 1 = 0 := by decide +kernel

theorem binding_cost_positive (I : Index) (hI : params.codec.Accepted I) (u : Fin 6) :
    0 < FusionCodec.cost (bindingUnit u) (FusionCodec.field (bindingUnit u) I) := by
  have hl := (FusionCodec.not_dummy_iff I).mp ((FusionCodec.accepted_iff I).mp hI).1
    (bindingUnit u) (bindingUnit_lt u)
  have hb := FusionCodec.cost_spec hl
  by_contra hn
  have hz : FusionCodec.cost (bindingUnit u) (FusionCodec.field (bindingUnit u) I) = 0 := by omega
  rw [hz, show 0+1=1 from rfl, bindingUnit_zero_empty u] at hb
  omega

theorem parents_sum (I : Index) (u : Fin 6) :
    ∑ k ∈ parents u, FusionCodec.digitN I k =
      FusionCodec.cost (bindingUnit u) (FusionCodec.field (bindingUnit u) I) := by
  have hh : ∀ v < 13,
      ∑ i ∈ Finset.range (FusionCodec.shK (FusionCodec.ushape v)),
        (FusionCodec.tup v (FusionCodec.field v I)).getD i 0 =
          FusionCodec.cost v (FusionCodec.field v I) := by
    intro v hv
    have hf := FusionCodec.field_lt' hv I
    rw [← FusionCodec.tup_sum hf, ← FusionCodec.sum_range_getD, FusionCodec.tup_length hf]
  have h := hh (bindingUnit u) (bindingUnit_lt u)
  fin_cases u <;>
    simpa [parents, bindingUnit, FusionCodec.digitN, FusionCodec.unitOf, FusionCodec.coordOf,
      FusionCodec.shK, FusionCodec.ushape, Finset.sum_range_succ, add_assoc] using h

/-- Every accepted signature executes a final binding step in each of the six groups. -/
theorem accepted_active (I : Index) (hI : params.codec.Accepted I) (u : Fin 6) :
    0 < ∑ k ∈ parents u, FusionCodec.digitN I k := by
  rw [parents_sum]
  exact binding_cost_positive I hI u

theorem accepted_parent (I : Index) (hI : params.codec.Accepted I) (u : Fin 6) :
    ∃ k : Fin 42, k.val ∈ parents u ∧ 0 < params.codec.digit I k := by
  have hpos := accepted_active I hI u
  by_contra hn
  have hz : ∀ k ∈ parents u, FusionCodec.digitN I k = 0 := by
    intro k hk
    have hlt := parents_bounded u k hk
    by_contra hne
    exact hn ⟨⟨k,hlt⟩,hk,by change 0 < FusionCodec.digitN I k; omega⟩
  have hs : (∑ k ∈ parents u, FusionCodec.digitN I k) = 0 :=
    Finset.sum_eq_zero hz
  omega

/-- Structural hypotheses required by the fused reconstruction security proof. -/
structure Params.SecurityHyp (P : Params) extends P.Hyp where
  ordered : P.locationOrder.Pairwise Earlier
  binding : ∀ I, P.codec.Accepted I → ∀ u : Fin 6,
    ∃ k : Fin 42, k.val ∈ parents u ∧ 0 < P.codec.digit I k

instance {P : Params} : Coe P.SecurityHyp P.Hyp := ⟨fun h => h.toHyp⟩

theorem params_securityHyp : params.SecurityHyp where
  toHyp := params_hyp
  ordered := concrete_ordered
  binding := accepted_parent

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
