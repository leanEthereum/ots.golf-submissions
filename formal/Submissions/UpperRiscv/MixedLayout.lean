import Submissions.UpperRiscv.MixedContext
import Submissions.UpperRiscv.Payload

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W W_toNat)
open Forest

/-- Cursor in the graph's payload order, including the final cursor at chain 32. -/
def cursor (k : ℕ) : ℕ := 32 * Payload.graphUnit k
/-- Offset in the wire payload (`Payload.wireUnit` in 32-bit units). -/
def wireOffset (k : ℕ) : ℕ := 32 * Payload.wireUnit k

theorem chainBits_units (k : Fin 32) : chainBits k = 32 * Payload.unitCount k := by
  unfold chainBits Payload.unitCount
  split_ifs <;> omega

theorem cursor_step (k : Fin 32) : cursor (k.val+1) = cursor k + chainBits k := by
  unfold cursor Payload.graphUnit chainBits
  split_ifs <;> omega

theorem cursor_zero : cursor 0 = 0 := rfl
theorem cursor_end : cursor 32 = 5376 := by decide

theorem wireOffset_aligned (k : Fin 32) : wireOffset k % 8 = 0 := by
  unfold wireOffset
  omega

theorem wireOffset_contained (k : Fin 32) : wireOffset k + chainBits k ≤ 5376 := by
  have h := Payload.wireUnit_add k k.isLt
  rw [chainBits_units k]
  unfold wireOffset
  omega

theorem wireSlot_eq (k : Fin 32) : wireSlot k = 0x400040 + wireOffset k / 8 := by
  unfold wireSlot wireOffset
  omega

theorem output_bounds' : ∀ k : Fin 32,
    0x400038 ≤ outAddr k ∧ outAddr k + 32 ≤ 0x4003E0 ∧ outAddr k % 8 = 0 := by
  decide +kernel

theorem output_bounds (k : Fin 32) :
    0x400038 ≤ outAddr k ∧ outAddr k + 32 ≤ 0x4003E0 ∧ outAddr k % 8 = 0 :=
  output_bounds' k

theorem slot_bounds (k : Fin 32) :
    0x400040 ≤ slot k ∧ slot k + 24 ≤ 0x4003E0 ∧ slot k % 8 = 0 := by
  have h := output_bounds k
  unfold slot
  omega

/-- The state of every chain begins `truncOff k / 8` bytes into its answer buffer. -/
theorem work_eq' : ∀ k : Fin 32, work k = outAddr k + truncOff k / 8 := by
  decide +kernel

theorem work_of_expands {k : ℕ} (h : expands k = true) : work k = slot k := by
  unfold work
  exact if_pos h

theorem work_of_not_expands {k : ℕ} (h : ¬ expands k = true) : work k = wireSlot k := by
  unfold work
  exact if_neg h

theorem work_bounds' : ∀ k : Fin 32, 32 ≤ work k ∧ work k + 24 ≤ 0x78000000 := by
  decide +kernel

theorem unread_disjoint' : ∀ k j : Fin 32, k.val < j.val →
    wireSlot j + chainBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ wireSlot j := by
  decide +kernel

/-- No chain hash overwrites a later, unread wire block. -/
theorem unread_disjoint (k j : Fin 32) (hkj : k.val < j.val) :
    wireSlot j + chainBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ wireSlot j :=
  unread_disjoint' k j hkj

/-- The root input: the 928 bytes after the nonce. -/
def rootAddr : ℕ := 0x400040

/-- Position of the bytes committed by the root for a completed chain. -/
def rootSliceAddr (k : ℕ) : ℕ := outAddr k + rootStart k / 8
def rootSliceBits (k : ℕ) : ℕ := rootWidth k

theorem rootSlice_bounds' : ∀ k : Fin 32,
    rootSliceAddr k + rootSliceBits k / 8 ≤ 0x4003E0 ∧ rootSliceBits k ≤ 256 ∧
      rootSliceBits k % 8 = 0 := by
  decide +kernel

theorem completed_disjoint' : ∀ j k : Fin 32, j.val < k.val →
    rootSliceAddr j + rootSliceBits j / 8 ≤ outAddr k ∨
      outAddr k + 32 ≤ rootSliceAddr j := by
  decide +kernel

/-- Every later hash preserves the committed slice of an earlier chain. -/
theorem completed_disjoint (j k : Fin 32) (hjk : j.val < k.val) :
    rootSliceAddr j + rootSliceBits j / 8 ≤ outAddr k ∨
      outAddr k + 32 ≤ rootSliceAddr j :=
  completed_disjoint' j k hjk

theorem payload_index (k : Fin 32) (i : ℕ) (hi : i < chainBits k) :
    Payload.index 5376 (cursor k + i) = wireOffset k + i := by
  rw [chainBits_units k] at hi
  unfold cursor wireOffset
  exact Payload.index_chain k k.isLt i hi

end OptimalOTS.RiscvMixedProgram
