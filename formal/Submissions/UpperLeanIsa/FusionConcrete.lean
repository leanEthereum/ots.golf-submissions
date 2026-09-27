import Submissions.UpperLeanIsa.LengthGate
import Submissions.UpperLeanIsa.FusionTier
import Submissions.UpperLeanIsa.FusionInputs

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open LeanerVM.Parameters

theorem length_ne_factor {c : ℕ} (hc : c < 45) :
    LeanIsaFieldRescale.costFactor c ≠ (5503 : K) := by
  intro h
  unfold LeanIsaFieldRescale.costFactor at h
  rw [← HLG3.gpow_mod, ← HLG3.LengthGate.log5503] at h
  have he := HLG3.gpow_inj
    (show (LeanIsaFieldRescale.stride*c) % HLG3.ordG < 2^64-1 from
      Nat.mod_lt _ (by norm_num [HLG3.ordG]))
    (show 4674821839435376859 < 2^64-1 by norm_num) h
  interval_cases c <;> norm_num [LeanIsaFieldRescale.stride, HLG3.ordG] at he

theorem sentinel_ne_factor {c : ℕ} (hc : c < 45) :
    gpow 262143 ≠ LeanIsaFieldRescale.costFactor c := by
  intro h
  have h' := h.symm
  unfold LeanIsaFieldRescale.costFactor at h'
  rw [← HLG3.gpow_mod] at h'
  have he := HLG3.gpow_inj
    (show (LeanIsaFieldRescale.stride*c) % HLG3.ordG < 2^64-1 from
      Nat.mod_lt _ (by norm_num [HLG3.ordG]))
    (show 262143 < 2^64-1 by norm_num) h'
  interval_cases c <;> norm_num [LeanIsaFieldRescale.stride, HLG3.ordG] at he

theorem sentinel_ne_length : gpow 262143 ≠ (5503 : K) := by
  intro h
  rw [← HLG3.LengthGate.log5503] at h
  have he := HLG3.gpow_inj (by norm_num) (by norm_num) h
  norm_num at he

def domainTag (i : Fin 47) : K :=
  if i.val < 45 then LeanIsaFieldRescale.costFactor i.val
  else if i.val = 45 then 5503 else gpow 262143

theorem domainTag_injective : Function.Injective domainTag := by
  intro i j h
  by_cases hi : i.val < 45 <;> by_cases hj : j.val < 45
  · simp only [domainTag, if_pos hi, if_pos hj] at h
    exact Fin.ext (LeanIsaFieldRescale.factor_injective (by omega) (by omega) h)
  · simp only [domainTag, if_pos hi, if_neg hj] at h
    split_ifs at h
    · exact (length_ne_factor (by omega) h).elim
    · exact (sentinel_ne_factor (by omega) h.symm).elim
  · simp only [domainTag, if_neg hi, if_pos hj] at h
    split_ifs at h
    · exact (length_ne_factor (by omega) h.symm).elim
    · exact (sentinel_ne_factor (by omega) h).elim
  · have hi' : i.val=45 ∨ i.val=46 := by have := i.isLt; omega
    have hj' : j.val=45 ∨ j.val=46 := by have := j.isLt; omega
    rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
    · exact Fin.ext (by omega)
    · simp [domainTag, hi', hj'] at h
      exact (sentinel_ne_length h.symm).elim
    · simp [domainTag, hi', hj'] at h
      exact (sentinel_ne_length h).elim
    · exact Fin.ext (by omega)

end OptimalOTS.LeanIsaBaseline.Layer.Fusion

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
  chain_idx := cv_ne_idxCv
  tier := ⟨FusionNumeric.schedule, FusionNumeric.schedule_valid, tierHyp⟩

end FusionCodec
namespace Fusion
open LeanerVM.Parameters
/-- Distinct labels make `fusedMd` injective on all chains. The executable program uses only
the root label `C_1`, the sixteen labels of the five-dep chains and the three-dep cv pairs. -/
def tagWord (i : Fin 47) : Word := (0 : BitVec 64) ++ (domainTag i : K)

theorem tagWord_injective : Function.Injective tagWord := by
  intro a b h
  apply domainTag_injective
  simpa only [tagWord, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun w : Word => w.extractLsb' 0 64) h

def tagIndex (k : Fin 42) : Fin 47 :=
  ![23,11,12,14,16,45,46,13,17,18,19,20,24,25,2,3,4,26,27,5,6,7,28,29,8,9,10,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44] k

def rootIndex (r : Fin 1) : Fin 47 := ![1] r

/-- The cv index `a` of a three-dep parent: its cv pair is `(C_a, C_(a+1))`. -/
def tripleIndex (k : Fin 42) : Fin 47 :=
  ![1,1,1,1,1,1,1,1,1,2,3,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,5,6,7,1,1,8,9,10,1,1,11,12,13] k

theorem tagIndex_injective : Function.Injective tagIndex := by decide +kernel

theorem tripleOwned_iff : ∀ k : Fin 42,
    tripleOwned k ↔ k.val ∈ [8,9,10,11,29,30,31,34,35,36,39,40,41] := by
  unfold tripleOwned
  decide

theorem tripleIndex_inj : ∀ k k' : Fin 42, k.val ∈ [8,9,10,11,29,30,31,34,35,36,39,40,41] →
    k'.val ∈ [8,9,10,11,29,30,31,34,35,36,39,40,41] → tripleIndex k = tripleIndex k' → k = k' := by
  decide

theorem tripleIndex_ne_zero : ∀ k, tripleIndex k ≠ 0 := by decide

theorem tripleIndex_ne_14 : ∀ k, tripleIndex k ≠ 14 := by decide

theorem tagIndex_reserved : ∀ k, tagIndex k ≠ 0 ∧ ∀ r, tagIndex k ≠ rootIndex r := by
  decide

theorem rootIndex_reserved : ∀ r, rootIndex r ≠ 0 := by decide +kernel

/-- The three-dep cv `(C_a, C_(a+1))` is the machine's adjacent constant cells `50 + a`, `51 + a`. -/
noncomputable def params : Params where
  codec := FusionCodec.params
  fusedMd k := tagWord (tagIndex k)
  rootMd r := tagWord (rootIndex r)
  tripleCv k := tagWord (tripleIndex k + 1) ++ tagWord (tripleIndex k)

attribute [local irreducible] tagWord LeanIsaFieldRescale.costFactor

theorem tagWord_small (i : Fin 47) (hi : i.val < 45) :
    tagWord i = (0 : BitVec 64) ++ LeanIsaFieldRescale.costFactor i.val := by
  unfold tagWord domainTag
  rw [if_pos hi]

theorem codec_chain_tag : params.codec.chainMd = tagWord 0 := by
  change FusionCodec.gword 0 = tagWord 0
  rw [tagWord_small 0 (by decide), FusionCodec.gword_eq]
  simp only [LeanIsaFieldRescale.costFactor, Fin.val_zero, Nat.mul_zero]


theorem params_hyp : params.Hyp where
  codec := FusionCodec.hyp
  fused_inj := tagWord_injective.comp tagIndex_injective
  fused_chain := by
    intro k h
    rw [codec_chain_tag] at h
    exact (tagIndex_reserved k).1 (tagWord_injective h)
  fused_idx := by
    intro k h
    rw [show params.codec.idxMd = tagWord 0 from codec_chain_tag] at h
    exact (tagIndex_reserved k).1 (tagWord_injective h)
  fused_root := by
    intro k r h
    exact (tagIndex_reserved k).2 r (tagWord_injective h)
  root_chain := by
    intro r h
    rw [codec_chain_tag] at h
    exact rootIndex_reserved r (tagWord_injective h)
  root_idx := by
    intro r h
    rw [show params.codec.idxMd = tagWord 0 from codec_chain_tag] at h
    exact rootIndex_reserved r (tagWord_injective h)
  triple_cv := by
    intro k h
    have hc : tagWord (tripleIndex k + 1) ++ tagWord (tripleIndex k) =
      FusionCodec.gword 1 ++ FusionCodec.gword 0 := h
    have h1 := (append_inj hc).2
    rw [show FusionCodec.gword 0 = tagWord 0 from codec_chain_tag] at h1
    exact tripleIndex_ne_zero k (tagWord_injective h1)
  triple_idx := by
    intro k h
    have hc : tagWord (tripleIndex k + 1) ++ tagWord (tripleIndex k) =
      FusionCodec.gword 262143 ++ FusionCodec.gword (1152921504606846976 * 14) := h
    have h1 := (append_inj hc).2
    rw [show FusionCodec.gword (1152921504606846976 * 14) = tagWord 14 by
      rw [tagWord_small 14 (by decide), FusionCodec.gword_eq]
      simp only [LeanIsaFieldRescale.costFactor, LeanIsaFieldRescale.stride]
      rfl] at h1
    exact tripleIndex_ne_14 k (tagWord_injective h1)
  triple_inj := by
    intro k k' hk hk' h
    have h1 := tagWord_injective (append_inj h).2
    exact tripleIndex_inj k k' ((tripleOwned_iff k).mp hk) ((tripleOwned_iff k').mp hk') h1

end Fusion
end OptimalOTS.LeanIsaBaseline.Layer
