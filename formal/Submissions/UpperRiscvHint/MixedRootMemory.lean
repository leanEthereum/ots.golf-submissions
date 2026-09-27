import Submissions.UpperRiscvHint.MixedRoot

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

theorem slotWidth_aligned : ∀ s : Fin 33, slotWidth s % 8 = 0 := by decide

/-- Root slot `s + 1` starts where slots `0 … s` end. -/
theorem slot_address : ∀ s : Fin 32, outAddr (slotChain (s.val + 1)) = regionAddr + slotWidth s / 8 := by
  decide

theorem completed_slotCat (s : MachineState) (c : (k : Chain) → BitVec (topBits k))
    (done : Completed s c 33) : ∀ n, n < 33 → MemBits s (W regionAddr) (slotCat c n) := by
  intro n
  induction n with
  | zero =>
    intro _
    have h := done (slotChain 0) (by decide)
    have e : outAddr (slotChain 0) = regionAddr := by decide
    rw [e] at h
    exact h
  | succ n ih =>
    intro hn
    rw [slotCat]
    apply memBits_append (slotWidth_aligned ⟨n, by omega⟩) (ih (by omega))
    have h := done (slotChain (n+1)) (Fin.isLt _)
    have e := slot_address ⟨n, by omega⟩
    dsimp only at e
    rw [e, ← W_add] at h
    exact h

/-- The completed tops form exactly the graph's 7104-bit root input. -/
theorem completed_root (s : MachineState) (c : (k : Chain) → BitVec (topBits k))
    (done : Completed s c 33) : MemBits s (W regionAddr) (rootCat c) := by
  unfold rootCat
  exact (memBits_cast _ _ _ _).mpr (completed_slotCat s c done 32 (by decide))

end OptimalOTS.RiscvMixedProgram
