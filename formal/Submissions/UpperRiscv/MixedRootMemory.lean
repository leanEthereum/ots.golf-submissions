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
    (done : Completed s c 32) (j : ℕ) (hj : j < 32) :
    MemBits s (W (regionAddr+24*j)) (lo192 (topFun c j)) := by
  have h := done ⟨j, hj⟩ (by omega)
  change MemBits s (W (rootSliceAddr j)) (rootSlice j (c ⟨j, hj⟩)) at h
  have ha : rootSliceAddr j = regionAddr+24*j := by
    unfold rootSliceAddr outAddr slot regionAddr
    omega
  rw [ha] at h
  intro i hi
  have h' := h i (by exact hi)
  simpa [rootSlice, rootSliceStart, rootSliceBits, lo192, hi, topFun, hj] using h'

theorem completed_lowCat (s : MachineState) (c : Fin 32 → BitVec 256)
    (done : Completed s c 32) : ∀ j, j < 32 →
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
    convert h using 1; congr 1; omega

/-- The completed slices form exactly the graph's 6144-bit root input. -/
theorem completed_root (s : MachineState) (c : Fin 32 → BitVec 256)
    (done : Completed s c 32) : MemBits s (W regionAddr) (rootCat c) := by
  have low := completed_lowCat s c done 31 (by decide)
  unfold rootCat
  exact (memBits_cast _ _ _ _).mpr low

end OptimalOTS.RiscvMixedProgram
