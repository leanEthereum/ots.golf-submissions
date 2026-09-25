import Submissions.UpperLeanIsa.LengthGate

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
