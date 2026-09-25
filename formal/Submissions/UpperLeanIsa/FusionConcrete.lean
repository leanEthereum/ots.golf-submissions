import Submissions.UpperLeanIsa.FusionTier
import Submissions.UpperLeanIsa.FusionInputs
import Submissions.UpperLeanIsa.FusionDomains

set_option Elab.async false

namespace OptimalOTS.LeanIsaBaseline.Layer
namespace FusionCodec
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
  tier := ⟨FusionNumeric.schedule, FusionNumeric.schedule_valid, tierHyp⟩
  keygen_le := by
    change 2 * (∑ k : Fin 42, (lenN k - 1)) + 18 ≤ 2 ^ 20
    rw [steps_eq]; norm_num
  verify_le := by change 20 + 2 * 86 ≤ 2 ^ 20; norm_num
  len_zero := by change 2 ≤ lenN 0; decide


end FusionCodec
namespace Fusion
open LeanerVM.Parameters
/-- The first 25 used domains plus 22 unused labels make `fusedMd` injective on all chains.
Only the twenty labels of actual binding chains occur in the executable program. -/
def tagWord (i : Fin 47) : Word := (0 : BitVec 64) ++ (domainTag i : K)

theorem tagWord_injective : Function.Injective tagWord := by
  intro a b h
  apply domainTag_injective
  simpa only [tagWord, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun w : Word => w.extractLsb' 0 64) h

def tagIndex (k : Fin 42) : Fin 47 :=
  ![23,11,12,14,15,45,46,13,17,18,19,20,24,25,2,3,4,26,27,5,6,7,28,29,8,9,10,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44] k

def rootIndex (r : Fin 3) : Fin 47 := ![1,21,22] r

theorem tagIndex_injective : Function.Injective tagIndex := by decide +kernel
theorem rootIndex_injective : Function.Injective rootIndex := by decide +kernel

theorem tagIndex_reserved : ∀ k, tagIndex k ≠ 0 ∧ tagIndex k ≠ 16 ∧ ∀ r, tagIndex k ≠ rootIndex r := by
  decide

theorem rootIndex_reserved : ∀ r, rootIndex r ≠ 0 ∧ rootIndex r ≠ 16 := by decide +kernel

noncomputable def params : Params where
  codec := FusionCodec.params
  fusedMd k := tagWord (tagIndex k)
  rootMd r := tagWord (rootIndex r)

attribute [local irreducible] tagWord LeanIsaFieldRescale.costFactor

theorem tagWord_small (i : Fin 47) (hi : i.val < 45) :
    tagWord i = (0 : BitVec 64) ++ LeanIsaFieldRescale.costFactor i.val := by
  unfold tagWord domainTag
  rw [if_pos hi]

theorem codec_chain_tag : params.codec.chainMd = tagWord 0 := by
  change FusionCodec.gword 0 = tagWord 0
  rw [tagWord_small 0 (by decide), FusionCodec.gword_eq]
  simp only [LeanIsaFieldRescale.costFactor, Fin.val_zero, Nat.mul_zero]

theorem codec_index_tag : params.codec.idxMd = tagWord 16 := by
  change FusionCodec.gword 1 = tagWord 16
  rw [tagWord_small 16 (by decide), FusionCodec.gword_eq]
  change (0 : BitVec 64) ++ gpow 1 = (0 : BitVec 64) ++ LeanIsaFieldRescale.costFactor 16
  rw [LeanIsaFieldRescale.factor_sixteen]
  congr 1

theorem params_hyp : params.Hyp where
  codec := FusionCodec.hyp
  fused_inj := tagWord_injective.comp tagIndex_injective
  fused_chain := by
    intro k h
    rw [codec_chain_tag] at h
    exact (tagIndex_reserved k).1 (tagWord_injective h)
  fused_idx := by
    intro k h
    rw [codec_index_tag] at h
    exact (tagIndex_reserved k).2.1 (tagWord_injective h)
  fused_root := by
    intro k r h
    exact (tagIndex_reserved k).2.2 r (tagWord_injective h)
  root_inj := tagWord_injective.comp rootIndex_injective
  root_chain := by
    intro r h
    rw [codec_chain_tag] at h
    exact (rootIndex_reserved r).1 (tagWord_injective h)
  root_idx := by
    intro r h
    rw [codec_index_tag] at h
    exact (rootIndex_reserved r).2 (tagWord_injective h)

end Fusion
end OptimalOTS.LeanIsaBaseline.Layer
