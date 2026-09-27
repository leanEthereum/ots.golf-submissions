import Submissions.UpperLeanIsa.AffineGuard
import Submissions.UpperLeanIsa.FourAdmissible
import Submissions.UpperLeanIsa.FourSecurity

/-! The existing layer-86 construction with domain words and cost symbols drawn
from the affine frame base. Its digit tables and signing schedule are unchanged. -/

namespace OptimalOTS.LeanIsaBaseline.Layer.AffineCodec

open LeanerVM.Parameters
open OptimalOTS.AffineFrames
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (L : Layout)

def word (i : ℕ) : Word := LeanIsa.cellBits (ofK (safeBase L ^ i))

theorem word_eq (i : ℕ) : word L i = (0 : BitVec 64) ++ (safeBase L ^ i : K) := by
  unfold word LeanIsa.cellBits
  rw [limb_ofK, limb_ofK]
  simp

theorem word_inj {i j : ℕ} (hi : i ≤ 300) (hj : j ≤ 300)
    (h : word L i = word L j) : i = j := by
  rw [word_eq, word_eq] at h
  have h' : safeBase L ^ i = safeBase L ^ j := by
    simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (64 + 64) => z.extractLsb' 0 64) h
  exact safeBase_powers_injective L hi hj h'

def tag (k : Fin numChains) (j : ℕ) : Fin 3 → Word :=
  ![word L ((FourChildCodec.off k + j) % 9),
    word L ((FourChildCodec.off k + j) / 9 % 9),
    word L ((FourChildCodec.off k + j) / 81)]

/-- Cell 49, formerly `g`, supplies the fourteenth stage bias and index metadata. -/
def codec : Layer.Params := { FourChildCodec.params with
  tag := tag L
  cv := word L 14 ++ word L 0
  chainMd := word L 0
  idxMd := word L 14
  rootMd r := word L (15+r) }

theorem tag_inj (k k' : Fin numChains) (j j' : ℕ)
    (hj : j + 1 < FourChildCodec.len k) (hj' : j' + 1 < FourChildCodec.len k')
    (h0 : tag L k j 0 = tag L k' j' 0) (h1 : tag L k j 1 = tag L k' j' 1)
    (h2 : tag L k j 2 = tag L k' j' 2) : k = k' ∧ j = j' := by
  unfold FourChildCodec.len at hj hj'
  obtain ⟨hp, hl⟩ := FourChildCodec.pos_facts k k.isLt j (by omega)
  obtain ⟨hp', hl'⟩ := FourChildCodec.pos_facts k' k'.isLt j' (by omega)
  simp only [tag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have e0 := word_inj L (by omega) (by omega) h0
  have e1 := word_inj L (by omega) (by omega) h1
  have e2 := word_inj L (by omega) (by omega) h2
  have hpp : FourChildCodec.off k + j = FourChildCodec.off k' + j' := by omega
  rw [hpp, hl'] at hl
  obtain ⟨hk, hjj⟩ := Prod.mk.inj hl
  exact ⟨Fin.ext hk.symm, hjj.symm⟩

theorem tierHyp : (codec L).TierHyp FourChildNumeric.schedule where
  K_eq := FourChildCodec.tierHyp.K_eq
  weight_mem := FourChildCodec.tierHyp.weight_mem
  card_weight := FourChildCodec.tierHyp.card_weight

theorem codec_hyp : (codec L).Hyp where
  len_pos := FourChildCodec.hyp.len_pos
  digit_lt := FourChildCodec.hyp.digit_lt
  layer_pos := FourChildCodec.hyp.layer_pos
  tag_inj := tag_inj L
  chain_idx := by
    intro h
    have := word_inj L (i:=0) (j:=14) (by decide) (by decide) h
    omega
  chain_root := by
    intro r hr h
    have := word_inj L (i:=0) (j:=15+r) (by omega) (by omega) h
    omega
  root_idx := by
    intro r hr h
    have := word_inj L (i:=15+r) (j:=14) (by omega) (by omega) h
    omega
  root_inj := by
    intro r s hr hs h
    have := word_inj L (i:=15+r) (j:=15+s) (by omega) (by omega) h
    omega
  tier := ⟨FourChildNumeric.schedule, FourChildNumeric.schedule_valid, tierHyp L⟩
  keygen_le := FourChildCodec.hyp.keygen_le
  verify_le := FourChildCodec.hyp.verify_le
  len_zero := FourChildCodec.hyp.len_zero

def params : FourFusion.Params where
  codec := codec L
  fusedMd k := word L (FourFusion.mdIndex k).val
  fusedTag k := word L (FourFusion.tagIndex k).val
  rootMd r := word L (FourFusion.rootIndex r).val

theorem md_reserved : ∀ k, FourFusion.mdIndex k ≠ 0 ∧ FourFusion.mdIndex k ≠ 14 ∧
    ∀ r, FourFusion.mdIndex k ≠ FourFusion.rootIndex r := by decide

theorem root_reserved : ∀ r, FourFusion.rootIndex r ≠ 0 ∧
    FourFusion.rootIndex r ≠ 14 := by decide

theorem word_fin_inj {i j : Fin 47} (h : word L i = word L j) : i = j :=
  Fin.ext (word_inj L (by have := i.isLt; omega) (by have := j.isLt; omega) h)

theorem params_hyp : (params L).Hyp where
  codec := codec_hyp L
  fused_inj := by
    intro a b h
    have he := Prod.mk.inj h
    exact FourFusion.indices_injective
      (Prod.ext (word_fin_inj L he.1) (word_fin_inj L he.2))
  fused_chain := fun k h => (md_reserved k).1 (word_fin_inj L h)
  fused_idx := fun k h => (md_reserved k).2.1 (word_fin_inj L h)
  fused_root := fun k r h => (md_reserved k).2.2 r (word_fin_inj L h)
  root_inj := fun _ _ _ => Subsingleton.elim _ _
  root_chain := fun r h => (root_reserved r).1 (word_fin_inj L h)
  root_idx := fun r h => (root_reserved r).2 (word_fin_inj L h)

theorem ordered : (params L).locationOrder.Pairwise FourFusion.Earlier := by
  have he : (@FourFusion.Earlier FourFusion.params) =
      (@FourFusion.Earlier (params L)) := by
    funext a b
    rcases a with ⟨k,j⟩ | r <;> rcases b with ⟨k',j'⟩ | r' <;> rfl
  rw [← he]
  exact FourFusion.concrete_ordered

theorem location_count : (params L).locationOrder.length = 720 :=
  FourFusion.concrete_location_count

theorem securityHyp : (params L).SecurityHyp where
  toHyp := params_hyp L
  ordered := ordered L
  binding := FourFusion.accepted_parent

theorem admissible : (params L).scheme.Admissible :=
  (params L).admissible (params_hyp L) (ordered L) FourChildNumeric.schedule_valid (tierHyp L)
    (by rw [location_count]; decide) (by change 4 + 2 * 86 ≤ verifyBudget; decide)

theorem secure : (params L).scheme.Secure := (params L).secure (securityHyp L)

end
end OptimalOTS.LeanIsaBaseline.Layer.AffineCodec
