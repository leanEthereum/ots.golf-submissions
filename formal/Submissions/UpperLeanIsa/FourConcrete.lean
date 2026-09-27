import Submissions.UpperLeanIsa.FourChildTier
import Submissions.UpperLeanIsa.FourInputs
import Submissions.UpperLeanIsa.FusionDomains

set_option Elab.async false

namespace OptimalOTS.LeanIsaBaseline.Layer
namespace FourChildCodec
theorem tag_inj (k k' : Fin numChains) (j j' : ℕ) (hj : j + 1 < len k) (hj' : j' + 1 < len k')
    (h0 : tag k j 0 = tag k' j' 0) (h1 : tag k j 1 = tag k' j' 1)
    (h2 : tag k j 2 = tag k' j' 2) : k = k' ∧ j = j' := by
  unfold len at hj hj'
  obtain ⟨hp, hl⟩ := pos_facts k k.isLt j (by omega)
  obtain ⟨hp', hl'⟩ := pos_facts k' k'.isLt j' (by omega)
  simp only [tag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have e0 := sym_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h0
  have e1 := sym_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
  have e2 := sym_inj (by omega) (by omega) h2
  have hpp : off k + j = off k' + j' := by omega
  rw [hpp, hl'] at hl
  obtain ⟨hk, hjj⟩ := Prod.mk.inj hl
  exact ⟨Fin.ext hk.symm, hjj.symm⟩

theorem hyp : params.Hyp where
  len_pos := fun k => (Nat.zero_le _).trans_lt (digit_lt 0 k)
  digit_lt := digit_lt
  layer_pos := by decide +kernel
  tag_inj := tag_inj
  chain_idx := chainMd_ne
  chain_root := chainMd_ne_root
  root_idx := rootMd_ne
  root_inj := rootMd_inj
  tier := ⟨FourChildNumeric.schedule, FourChildNumeric.schedule_valid, tierHyp⟩
  keygen_le := by
    change 2 * (∑ k : Fin 42, (lenN k - 1)) + 18 ≤ 2 ^ 20
    rw [steps_eq]; norm_num
  verify_le := by change 20 + 2 * 86 ≤ 2 ^ 20; norm_num
  len_zero := by change 2 ≤ lenN 0; decide


end FourChildCodec
namespace FourFusion
open LeanerVM.Parameters
abbrev tagWord := Fusion.tagWord
abbrev tagWord_injective := Fusion.tagWord_injective
abbrev tagWord_small := Fusion.tagWord_small

def mdIndex (k : Fin 42) : Fin 47 := ![6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 2, 2, 6, 6, 2, 2, 2, 6, 6, 2, 2, 2, 6, 6, 2, 2, 3, 6, 6, 3, 3, 3, 6, 6, 3, 3, 3] k

def tagIndex (k : Fin 42) : Fin 47 := ![1, 9, 10, 1, 2, 3, 4, 11, 5, 6, 7, 8, 2, 3, 13, 1, 2, 4, 5, 4, 5, 6, 6, 7, 8, 9, 10, 8, 9, 12, 13, 1, 10, 11, 3, 4, 5, 12, 13, 7, 8, 9] k

def rootIndex (_r : Fin 1) : Fin 47 := 4

theorem indices_injective : Function.Injective fun k => (mdIndex k,tagIndex k) := by decide +kernel

theorem mdIndex_reserved : ∀ k, mdIndex k ≠ 0 ∧ mdIndex k ≠ 16 ∧ ∀ r, mdIndex k ≠ rootIndex r := by decide

theorem rootIndex_reserved : ∀ r, rootIndex r ≠ 0 ∧ rootIndex r ≠ 16 := by decide

noncomputable def params : Params where
  codec := FourChildCodec.params
  fusedMd k := tagWord (mdIndex k)
  fusedTag k := tagWord (tagIndex k)
  rootMd r := tagWord (rootIndex r)

theorem codec_chain_tag : params.codec.chainMd = tagWord 0 := by
  change FourChildCodec.gword 0 = Fusion.tagWord 0
  rw [tagWord_small 0 (by decide), FourChildCodec.gword_eq]
  simp only [LeanIsaFieldRescale.costFactor, Fin.val_zero, Nat.mul_zero]

theorem codec_index_tag : params.codec.idxMd = tagWord 16 := by
  change FourChildCodec.gword 1 = Fusion.tagWord 16
  rw [tagWord_small 16 (by decide), FourChildCodec.gword_eq]
  change (0 : BitVec 64) ++ gpow 1 = (0 : BitVec 64) ++ LeanIsaFieldRescale.costFactor 16
  rw [LeanIsaFieldRescale.factor_sixteen]
  congr 1

theorem params_hyp : params.Hyp where
  codec := FourChildCodec.hyp
  fused_inj := by
    intro a b h
    have he := Prod.mk.inj h
    exact indices_injective (Prod.ext (tagWord_injective he.1) (tagWord_injective he.2))
  fused_chain := by
    intro k h
    rw [codec_chain_tag] at h
    exact (mdIndex_reserved k).1 (tagWord_injective h)
  fused_idx := by
    intro k h
    rw [codec_index_tag] at h
    exact (mdIndex_reserved k).2.1 (tagWord_injective h)
  fused_root := by
    intro k r h
    exact (mdIndex_reserved k).2.2 r (tagWord_injective h)
  root_inj := fun _ _ _ => Subsingleton.elim _ _
  root_chain := by
    intro r h
    rw [codec_chain_tag] at h
    exact (rootIndex_reserved r).1 (tagWord_injective h)
  root_idx := by
    intro r h
    rw [codec_index_tag] at h
    exact (rootIndex_reserved r).2 (tagWord_injective h)

end FourFusion
end OptimalOTS.LeanIsaBaseline.Layer
