import Submissions.UpperLeanIsa.FourChildTier
import Submissions.UpperLeanIsa.SplitDomains
import Submissions.UpperLeanIsa.FusionDomains
import Submissions.UpperLeanIsa.FusionConcrete
import Submissions.UpperLeanIsa.FourAdmissible

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
  verify_le := by change 20 + 2 * 85 ≤ 2 ^ 20; norm_num
  len_zero := by change 2 ≤ lenN 0; decide


end FourChildCodec
namespace FourFusion
open LeanerVM.Parameters
abbrev tagWord := Fusion.tagWord
abbrev tagWord_injective := Fusion.tagWord_injective
abbrev tagWord_small := Fusion.tagWord_small

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
  fused_inj := packet_location params
    (fun _ _ h => tagWord_injective h) (fun _ _ h => tagWord_injective h)
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem concrete_ordered : params.locationOrder.Pairwise Earlier := by
  haveI : IsTrans (Loc params) Earlier := ⟨fun _ _ _ => earlier_trans⟩
  apply List.isChain_iff_pairwise.mp
  decide +kernel

theorem concrete_location_count : params.locationOrder.length = 720 := by decide +kernel

/-- Coherence of every key-generation output for any fixed oracle, with no good-event assumption. -/
theorem concrete_coherent (f : HashTable) (seeds : Fin 42 → Word) :
    let y := params.evalLocationsValue f seeds params.locationOrder (fun _ => 0)
    ∀ a : Loc params, y a = f ⟨896,Record.input (seeds,y) a⟩ := by
  intro y a
  exact params.evalLocationsValue_coherent f seeds _ concrete_ordered _ a (params.locationOrder_mem a)


theorem concrete_correct : params.scheme.Correct :=
  params.correct params_hyp.codec concrete_ordered


theorem concrete_signingFailure :
    params.scheme.SigningFailureAtMost (1 / 2 ^ signingFailureBits) :=
  params.signingFailure params_hyp concrete_ordered FourChildNumeric.schedule_valid FourChildCodec.tierHyp


theorem concrete_keygenCost : CostAtMost params.keygen 1440 := by
  have h := params.cost_keygen
  rwa [concrete_location_count] at h

theorem concrete_verifyCost (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (params.verify pk m bits) 174 := params.cost_verify pk m bits

theorem concrete_admissible : params.scheme.Admissible :=
  params.admissible params_hyp concrete_ordered FourChildNumeric.schedule_valid FourChildCodec.tierHyp
    (by rw [concrete_location_count]; decide) (by decide)

end FourFusion
end OptimalOTS.LeanIsaBaseline.Layer
