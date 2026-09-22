import Submissions.UpperRiscv.MixedRoot

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

theorem lo192_extract (y : BitVec 256) : lo192 y = y.extractLsb' 0 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [lo192, hi]

theorem completed_low (s : MachineState) (c : Fin 32 → BitVec 256)
    (done : Completed s c 32) (j : ℕ) (hj : j < 7) :
    MemBits s (W (regionAddr+24*j)) (lo192 (topFun c j)) := by
  have h := done ⟨j, by omega⟩ (by omega)
  change MemBits s (W (rootSliceAddr j)) (rootSlice j (c ⟨j, by omega⟩)) at h
  have hb : j < 8 := by omega
  have hn : ¬(j=7 ∨ j=31) := by omega
  have ha : rootSliceAddr j = regionAddr+24*j := by
    unfold rootSliceAddr outAddr slot physical narrow regionAddr
    simp only [hb, true_or, if_true, show ¬8 ≤ j by omega, decide_false, Bool.false_eq_true, if_false]
    omega
  rw [ha] at h
  intro i hi
  have hw : rootSliceBits j = 192 := by simp only [rootSliceBits, hn, if_false]
  have h' := h i (by rw [hw]; exact hi)
  simpa [rootSlice, rootSliceStart, rootSliceBits, hb, hn, lo192, hi,
    topFun, show j < 32 by omega] using h'

theorem completed_high (s : MachineState) (c : Fin 32 → BitVec 256)
    (done : Completed s c 32) (j : ℕ) (hj : j ≤ 22) :
    MemBits s (W (slot (j+8))) ((topFun c (j+8)).extractLsb' 64 192) := by
  have h := done ⟨j+8, by omega⟩ (by omega)
  change MemBits s (W (rootSliceAddr (j+8))) (rootSlice (j+8) (c ⟨j+8, by omega⟩)) at h
  have hb : ¬(j+8 < 8 ∨ j+8 = 31) := by omega
  have hn : ¬(j+8=7 ∨ j+8=31) := by omega
  have ha : rootSliceAddr (j+8) = slot (j+8) := by simp only [rootSliceAddr, hb, if_false]
  rw [ha] at h
  intro i hi
  have hw : rootSliceBits (j+8) = 192 := by simp only [rootSliceBits, hn, if_false]
  have h' := h i (by rw [hw]; exact hi)
  simpa [rootSlice, rootSliceStart, rootSliceBits, hb, hn, hi,
    topFun, show j+8 < 32 by omega, show j ≠ 23 by omega] using h'

theorem completed_lowCat (s : MachineState) (c : Fin 32 → BitVec 256)
    (done : Completed s c 32) : ∀ j, j < 7 →
      MemBits s (W regionAddr) (lowCat (topFun c) j) := by
  intro j
  induction j with
  | zero => intro _; simpa [lowCat] using completed_low s c done 0 (by omega)
  | succ j ih =>
    intro hj
    rw [lowCat]
    apply (memBits_cast _ _ _ _).mpr
    apply memBits_append (by omega) (ih (by omega))
    have h := completed_low s c done (j+1) hj
    rw [W_add]
    convert h using 1 <;> congr 1 <;> omega

theorem completed_highCat (s : MachineState) (c : Fin 32 → BitVec 256)
    (done : Completed s c 32) : ∀ j, j ≤ 22 →
      MemBits s (W (slot (j+8))) (highCat (fun i => topFun c (i+8)) j) := by
  intro j
  induction j with
  | zero => intro _; exact completed_high s c done 0 (by omega)
  | succ j ih =>
    intro hj
    rw [highCat]
    apply (memBits_cast _ _ _ _).mpr
    apply memBits_append (by decide) (completed_high s c done (j+1) hj)
    have h := ih (by omega)
    rw [W_add]
    have e : slot (j+1+8)+192/8 = slot (j+8) := by
      unfold slot physical narrow
      simp only [show ¬j+1+8 < 8 by omega, show ¬j+8 < 8 by omega,
        if_false, show 8 ≤ j+1+8 by omega, show 8 ≤ j+8 by omega, decide_true, if_true]
      omega
    rw [e]
    exact h

/-- The completed slices form exactly the graph's 6272-bit root input. -/
theorem completed_root (s : MachineState) (c : Fin 32 → BitVec 256)
    (done : Completed s c 32) : MemBits s (W regionAddr) (rootCat c) := by
  have low := completed_lowCat s c done 6 (by decide)
  have high := completed_highCat s c done 22 (by decide)
  have wide := done 7 (by decide)
  have narrow := done 31 (by decide)
  change MemBits s (W (rootSliceAddr 7)) (rootSlice 7 (c 7)) at wide
  change MemBits s (W (rootSliceAddr 31)) (rootSlice 31 (c 31)) at narrow
  have e7 : rootSlice 7 (c 7) = c 7 := by simp [rootSlice, rootSliceBits, rootSliceStart]
  have e31 : rootSlice 31 (c 31) = c 31 := by simp [rootSlice, rootSliceBits, rootSliceStart]
  rw [e7] at wide
  rw [e31] at narrow
  unfold rootCat
  apply (memBits_cast _ _ _ _).mpr
  apply memBits_append (by decide) low
  apply memBits_append (by decide) wide
  apply memBits_append (by decide) narrow
  exact high

end OptimalOTS.RiscvMixedProgram
