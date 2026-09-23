import Submissions.UpperRiscv.MixedRoot

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

/-- The committed slice of the `i`-th chain in memory order is the `i`-th piece of the root. -/
theorem rootSliceAddr_piece' : ∀ i : Fin 32,
    rootSliceAddr (rootChain i) = rootAddr + rootOff i / 8 := by
  decide +kernel

theorem rootOff_aligned' : ∀ i : Fin 32, rootOff i % 8 = 0 := by
  decide +kernel

theorem rootSliceAddr_piece (i : ℕ) (hi : i < 32) :
    rootSliceAddr (rootChain i) = rootAddr + rootOff i / 8 :=
  rootSliceAddr_piece' ⟨i, hi⟩

theorem rootOff_aligned (i : ℕ) (hi : i < 32) : rootOff i % 8 = 0 :=
  rootOff_aligned' ⟨i, hi⟩

/-- The completed slices of the first `n` chains in memory order form the first `n` pieces. -/
theorem completed_part (s : MachineState) (c : Fin 32 → BitVec 256)
    (done : Completed s c 32) (n : ℕ) : n ≤ 32 → MemBits s (W rootAddr) (rootPart c n) := by
  induction n with
  | zero =>
    intro _ i hi
    first
    | exact absurd hi (Nat.not_lt_zero _)
    | (simp only [rootOff] at hi; omega)
  | succ n ih =>
    intro hn
    rw [rootPart]
    apply (memBits_cast _ _ _ _).mpr
    apply memBits_append (rootOff_aligned n (by omega)) (ih (by omega))
    have h := done (rootChain n) (rootChain n).isLt
    rw [rootSliceAddr_piece n (by omega)] at h
    rw [W_add]
    exact h

/-- The completed slices form exactly the graph's 7424-bit root input. -/
theorem completed_root (s : MachineState) (c : Fin 32 → BitVec 256)
    (done : Completed s c 32) : MemBits s (W rootAddr) (rootCat c) := by
  unfold rootCat
  exact (memBits_cast _ _ _ _).mpr (completed_part s c done 32 le_rfl)

end OptimalOTS.RiscvMixedProgram
