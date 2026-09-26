import Submissions.UpperLeanIsa.FusionMachineProgram
import Submissions.UpperLeanIsa.FusionConcrete

/-! Concrete raw tables and their relation to the 127-bit effective index. -/

namespace OptimalOTS.HLFusion
open LeanerVM.Parameters
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits)
noncomputable section

theorem list_sum_range (F : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ,List.map_append,List.sum_append,ih,Finset.sum_range_succ]; simp

/-- The low bit of the first raw field aliases the same tuple. -/
def rawCode (u v : ℕ) : ℕ := if u = 0 then v / 2 else v

def fusionTab : Tab := fun u v i => (FusionCodec.tup u (rawCode u v)).getD i 0

theorem shape_eq : ∀ u < 13, FusionCodec.shK (FusionCodec.ushape u) = gk u ∧
    FusionCodec.shB (FusionCodec.ushape u) = (if u = 0 then 9 else gb u) ∧
      FusionCodec.ubits u = (if u = 0 then 9 else gb u) := by decide

theorem rawCode_lt {u v : ℕ} (hu : u < 13) (hv : v < 2 ^ gb u) :
    rawCode u v < 2 ^ FusionCodec.shB (FusionCodec.ushape u) := by
  rw [(shape_eq u hu).2.1]
  unfold rawCode
  by_cases h0 : u = 0
  · subst u; norm_num [gb] at hv ⊢; omega
  · rw [if_neg h0, if_neg h0]; exact hv

theorem AS_eq : ∀ u < 13, ∀ c ≤ 17,
    A u c = (if u = 0 then 2 else 1) * FusionCodec.AS (FusionCodec.ushape u) c := by decide

theorem A_top : ∀ u < 13, ∀ c ≤ 18, nb u ≤ c → A u c = VF u := by decide

/-- The live entries of the scheme's tables are the machine's blocks. -/
theorem cut_eq : ∀ u < 13, FusionCodec.cut u = if u = 0 then 511 else VF u := by decide

theorem live_iff {u : ℕ} (hu : u < 13) (v : ℕ) (hv : v < 2 ^ gb u) :
    rawCode u v < FusionCodec.cut u ↔ v < VF u := by
  rw [cut_eq u hu]
  unfold rawCode
  by_cases h0 : u = 0
  · subst u; norm_num [gb, VF] at hv ⊢; omega
  · rw [if_neg h0, if_neg h0]

theorem chainAt_eq : ∀ u < 13, ∀ i < gk u, FusionCodec.chainAt u i = chainOf u i := by decide

theorem lenN_eq : ∀ k < 42, FusionCodec.lenN k = LEN k := by decide

theorem off_eq : ∀ k < 42, FusionCodec.off k = OFFT k := by decide

theorem unitOf_eq : ∀ k < 42, 1 ≤ k → FusionCodec.unitOf k = unitOf k ∧ FusionCodec.coordOf k = coordOf k := by
  decide

theorem shLen_eq : ∀ u < 13, ∀ i < gk u,
    FusionCodec.shLen (FusionCodec.ushape u) i = LEN (chainOf u i) := by decide

theorem effective_toNat (I : Word) : (effective I).toNat = I.toNat / 2 := by
  have hi := I.isLt
  simp only [effective, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  norm_num
  norm_num at hi
  omega

theorem posW_raw : ∀ u ≤ 13, posW FusionCodec.ubits u = if u = 0 then 0 else POS u - 1 := by decide

theorem field_eq {u : ℕ} (hu : u < 13) (I : Word) :
    FusionCodec.field u (effective I) = rawCode u (field u I) := by
  unfold FusionCodec.field field digitW
  rw [effective_toNat, posW_raw u (by omega), (shape_eq u hu).2.2]
  unfold rawCode
  interval_cases u <;> norm_num [POS, gb, posW] <;> omega

theorem fusion_cost_eq {u v : ℕ} (hu : u < 13) (hv : v < 2 ^ gb u) :
    cost fusionTab u v = FusionCodec.cost u (rawCode u v) := by
  have hk := (shape_eq u hu).1
  have hv' := rawCode_lt hu hv
  have hl := FusionCodec.tup_length hv'
  unfold cost fusionTab
  rw [← hk, ← hl, list_sum_range, FusionCodec.sum_range_getD, FusionCodec.tup_sum hv']

theorem fusion_band_eq {u v : ℕ} (hu : u < 13) (hvl : v < VF u) :
    FusionCodec.cost u (rawCode u v) = band u v := by
  have hv : v < 2 ^ gb u := lt_of_lt_of_le hvl (VF_le u hu)
  have hcut : rawCode u v < FusionCodec.cut u := (live_iff hu v hv).mpr hvl
  obtain ⟨h1, h2⟩ := FusionCodec.cost_spec hcut
  have hc : FusionCodec.cost u (rawCode u v) < 17 := FusionCodec.cost_lt hcut
  have ha := AS_eq u hu _ (show FusionCodec.cost u (rawCode u v) ≤ 17 by omega)
  have hb := AS_eq u hu _ (show FusionCodec.cost u (rawCode u v) + 1 ≤ 17 by omega)
  have h1' : A u (FusionCodec.cost u (rawCode u v)) ≤ v := by
    rw [ha]; by_cases h0 : u = 0 <;> simp only [rawCode, h0, if_true, if_false] at h1 ⊢ <;> omega
  have h2' : v < A u (FusionCodec.cost u (rawCode u v) + 1) := by
    rw [hb]; by_cases h0 : u = 0 <;> simp only [rawCode, h0, if_true, if_false] at h2 ⊢ <;> omega
  have hnb : FusionCodec.cost u (rawCode u v) < nb u := by
    by_contra h
    rw [A_top u hu _ (by omega) (by omega)] at h1'; omega
  exact (bandIdx_eq (A_mono u) hnb h1' h2').symm

theorem fusionTab_hyp : fusionTab.Hyp where
  cost_eq u hu v hv := by
    rw [fusion_cost_eq hu (lt_of_lt_of_le hv (VF_le u hu)), fusion_band_eq hu hv]
  coord_lt u hu v hv i hi := by
    have hk := (shape_eq u hu).1
    have hv' := rawCode_lt hu hv
    have h := FusionCodec.tupS_lt (FusionCodec.ushape_lt u) hv' (i := i) (by rw [hk]; exact hi)
    rw [shLen_eq u hu i hi] at h
    exact h

theorem fusion_freeDigit (c : ℕ) : FusionCodec.freeDigit c = freeDigit c := by
  unfold FusionCodec.freeDigit freeDigit
  split_ifs <;> omega

theorem fusion_gsum (I : Word) : FusionCodec.gsum (effective I) = gcost fusionTab I := by
  unfold FusionCodec.gsum gcost
  rw [list_sum_range]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  rw [field_eq hu' I, fusion_cost_eq hu' (by rw [field]; exact digitW_lt _ _ _)]

theorem cellBits_gpow_one : cellBits (ofK (gpow 1)) = cellBits gV := by
  unfold gV; rw [show gpow 1 = g from pow_one g]

theorem cellBits_gpow_zero : cellBits (ofK (gpow 0)) = cellBits oneV := by
  unfold oneV; rw [gpow_zero']

theorem params_digit (I : Index) (k : Fin numChains) : Fusion.params.codec.digit I k = FusionCodec.digit I k := rfl

theorem fusion_compat : Compat Fusion.params fusionTab where
  len k := lenN_eq k.val k.isLt
  layer := rfl
  digit_grp I u i hu hi := by
    have hk := chainOf_lt u hu i hi
    have hk1 := chainOf_pos u hu i hi
    obtain ⟨e1, e2⟩ := unitOf_eq _ hk hk1
    rw [params_digit, FusionCodec.digit_group (effective I) ⟨chainOf u i, hk⟩ (show chainOf u i ≠ 0 by omega)]
    simp only [e1, e2, unitOf_chainOf u hu i hi, coordOf_chainOf u hu i hi, field_eq hu]
    rfl
  digit_free I hl := by
    rw [params_digit, FusionCodec.digit_free_live (fun u hu => by
        rw [field_eq hu]; exact (live_iff hu _ (digitW_lt _ _ _)).mpr (hl u hu)),
      fusion_freeDigit, fusion_gsum]
  live I hacc u hu := by
    have h := ((FusionCodec.not_dummy_iff _).mp ((FusionCodec.accepted_iff _).mp hacc).1) u hu
    rw [field_eq hu] at h
    exact (live_iff hu _ (digitW_lt _ _ _)).mp h
  tag k j _ := by
    refine ⟨?_, ?_, ?_⟩ <;>
    · show FusionCodec.gword _ = _
      rw [off_eq k.val k.isLt]
      rfl
  hiTop _ := rfl
  cv := by
    change FusionCodec.gword 1 ++ FusionCodec.gword 0 = cellBits gV ++ cellBits oneV
    unfold FusionCodec.gword
    rw [cellBits_gpow_one, cellBits_gpow_zero]
  chainMd := cellBits_gpow_zero
  idxMd := cellBits_gpow_one
  fusedMd _ := rfl
  rootMd r := by
    change Fusion.tagWord (Fusion.rootIndex r) = _
    rw [Fusion.tagWord_small _ (by fin_cases r <;> decide)]
    rfl

end
end OptimalOTS.HLFusion
