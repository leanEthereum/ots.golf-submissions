import Submissions.UpperLeanIsa.AffineCompat
import Submissions.UpperLeanIsa.AffineCodec
import Submissions.UpperLeanIsa.FourMachineTable

namespace OptimalOTS.AffineVM
open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer OptimalOTS.LeanIsa
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem concrete_compat : Compat (AffineCodec.params (layout fusionTab)) fusionTab where
  len k := lenN_eq k.val k.isLt
  layer := rfl
  digit_grp I u i hu hi := by
    have hk := chainOf_lt u hu i hi
    have hk1 := chainOf_pos u hu i hi
    obtain ⟨e1, e2⟩ := unitOf_eq _ hk hk1
    change FourChildCodec.digit (effective I) ⟨chainOf u i, hk⟩ = _
    rw [FourChildCodec.digit_group (effective I) ⟨chainOf u i, hk⟩
      (show chainOf u i ≠ 0 by omega)]
    simp only [e1, e2, unitOf_chainOf u hu i hi, coordOf_chainOf u hu i hi, field_eq hu]
    rfl
  digit_free I hl := by
    change FourChildCodec.digit (effective I) 0 = _
    rw [FourChildCodec.digit_free_live (fun u hu => by
        rw [field_eq hu]; exact (live_iff hu _ (digitW_lt _ _ _)).mpr (hl u hu)),
      fusion_freeDigit, fusion_gsum]
  live I hacc u hu := by
    change FourChildCodec.params.Accepted (effective I) at hacc
    have h := ((FourChildCodec.not_dummy_iff _).mp
      ((FourChildCodec.accepted_iff _).mp hacc).1) u hu
    rw [field_eq hu] at h
    exact (live_iff hu _ (digitW_lt _ _ _)).mp h
  tag k j _ := by
    refine ⟨?_,?_,?_⟩ <;>
    · change AffineCodec.word (layout fusionTab) _ = _
      rw [off_eq k.val k.isLt]
      rfl
  hiTop _ := rfl
  cv := rfl
  chainMd := by
    change cellBits (ofK (base fusionTab^0)) = cellBits oneV
    rw [pow_zero]
    rfl
  idxMd := rfl
  fusedMd _ := rfl
  fusedTag _ := rfl
  rootMd _ := rfl


end
end OptimalOTS.AffineVM
